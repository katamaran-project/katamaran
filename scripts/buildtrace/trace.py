#!/usr/bin/env python3
"""Turn a build trace into a Chrome trace event file for https://ui.perfetto.dev.

Usage: trace.py BUILDTRACE DEPFILE [-o TRACE.json] [--top N]

BUILDTRACE is written by scripts/buildtrace/stamp (make BUILDTRACE=FILE), and
DEPFILE is the dependency file of Makefile.coq (.Makefile.coq.d). Prints a
summary: the slowest files, the critical path through the build and the files
that waited longest for a free job.

The trace has these tracks:
- build: one row per make job with a slice per file, and an arrow from the
  dependency each file waited for last; counters for the number of files
  compiling and the number of files whose dependencies are done but that wait
  for a free job.
- critical path: the chain of files that determined the build's end, as it
  ran, with the time each of them waited for a free job.
- unlimited jobs: the longest chain of dependencies, starting each file as soon
  as its dependencies are done. Its length is a lower bound on the build time
  for any number of jobs.
"""

import argparse
import json
import re


def read_trace(path):
    """Return {file: (start, end, status)}, keeping the last record of a file."""
    records = {}
    with open(path) as f:
        for line in f:
            start, end, status, file = line.split(maxsplit=3)
            records[file.strip()] = (float(start), float(end), int(status))
    return records


def read_deps(path, files):
    """Return {file: [direct dependencies]}, restricted to the given files."""
    with open(path) as f:
        text = f.read().replace("\\\n", " ")
    deps = {file: [] for file in files}
    for line in text.splitlines():
        targets, sep, prereqs = line.partition(":")
        if not sep:
            continue
        for target in targets.split():
            if target.endswith(".vo") and target[:-1] in deps:
                deps[target[:-1]] = [
                    p[:-1] for p in prereqs.split()
                    if p.endswith(".vo") and p[:-1] in files
                ]
    return deps


def assign_lanes(records):
    """Give each file the lowest-numbered job that is free when it starts."""
    lane_end, lanes = [], {}
    for file in sorted(records, key=lambda f: records[f][0]):
        start, end, _ = records[file]
        for i, free_at in enumerate(lane_end):
            if free_at <= start:
                break
        else:
            i = len(lane_end)
            lane_end.append(0)
        lane_end[i] = end
        lanes[file] = i
    return lanes


def longest_chain(files, dur, deps):
    """Earliest finish of each file with unlimited jobs, and its critical dep."""
    finish, via = {}, {}

    def visit(f):
        if f not in finish:
            ready = 0.0
            via[f] = None
            for d in deps[f]:
                if visit(d) > ready:
                    ready, via[f] = finish[d], d
            finish[f] = ready + dur[f]
        return finish[f]

    for f in files:
        visit(f)
    return finish, via


def chain(last, prev):
    path = []
    while last is not None:
        path.append(last)
        last = prev[last]
    return path[::-1]


def counters(events, name, t0):
    """Counter events for a list of (time, +1/-1) steps."""
    out, value = [], 0
    for t, step in sorted(events):
        value += step
        out.append({"name": name, "ph": "C", "pid": 1, "ts": us(t - t0),
                    "args": {name: value}})
    return out


def us(seconds):
    return round(seconds * 1e6)


def name(file):
    return re.sub(r"\.v$", "", file)


def fmt(seconds):
    return f"{seconds:8.1f}s"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("buildtrace")
    ap.add_argument("depfile")
    ap.add_argument("-o", "--output", default="trace.json")
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()

    records = read_trace(args.buildtrace)
    files = sorted(records)
    deps = read_deps(args.depfile, set(files))
    start = {f: records[f][0] for f in files}
    end = {f: records[f][1] for f in files}
    dur = {f: end[f] - start[f] for f in files}
    t0, t1 = min(start.values()), max(end.values())
    lanes = assign_lanes(records)

    # When each file's dependencies were done, and which one was done last.
    ready, blocker = {}, {}
    for f in files:
        ready[f], blocker[f] = t0, None
        for d in deps[f]:
            if end[d] > ready[f]:
                ready[f], blocker[f] = end[d], d
    queued = {f: start[f] - ready[f] for f in files}

    critical = chain(max(files, key=end.get), blocker)
    finish, via = longest_chain(files, dur, deps)
    ideal = chain(max(files, key=finish.get), via)
    on_critical = set(critical)

    # Latest finish of each file with unlimited jobs that does not delay the
    # build beyond the longest chain; the difference is the file's slack.
    bound = max(finish.values())
    latest = {f: bound for f in files}
    for f in sorted(files, key=finish.get, reverse=True):
        for d in deps[f]:
            latest[d] = min(latest[d], latest[f] - dur[f])

    ev = [
        {"name": "process_name", "ph": "M", "pid": 1, "args": {"name": "build"}},
        {"name": "process_sort_index", "ph": "M", "pid": 1,
         "args": {"sort_index": 1}},
        {"name": "process_name", "ph": "M", "pid": 2,
         "args": {"name": "critical path"}},
        {"name": "process_sort_index", "ph": "M", "pid": 2,
         "args": {"sort_index": 2}},
        {"name": "thread_name", "ph": "M", "pid": 2, "tid": 1,
         "args": {"name": "as built"}},
        {"name": "thread_name", "ph": "M", "pid": 2, "tid": 2,
         "args": {"name": "unlimited jobs"}},
    ]
    for i in range(max(lanes.values()) + 1):
        ev.append({"name": "thread_name", "ph": "M", "pid": 1, "tid": i + 1,
                   "args": {"name": f"job {i + 1}"}})

    for n, f in enumerate(files):
        ev.append({
            "name": name(f), "cat": f.split("/")[0], "ph": "X",
            "pid": 1, "tid": lanes[f] + 1,
            "ts": us(start[f] - t0), "dur": us(dur[f]),
            "args": {
                "file": f,
                "seconds": round(dur[f], 2),
                "waited for": name(blocker[f]) if blocker[f] else None,
                "queued for a job (s)": round(queued[f], 2),
                "slack (s)": round(latest[f] - finish[f], 2),
                "on critical path": f in on_critical,
                "dependencies": [name(d) for d in deps[f]],
                "status": records[f][2],
            },
        })
        if blocker[f]:
            b = blocker[f]
            ev.append({"name": "waited for", "cat": "dep", "ph": "s", "id": n,
                       "pid": 1, "tid": lanes[b] + 1,
                       "ts": us(end[b] - t0) - 1})
            ev.append({"name": "waited for", "cat": "dep", "ph": "f",
                       "bp": "e", "id": n, "pid": 1, "tid": lanes[f] + 1,
                       "ts": us(start[f] - t0)})

    for f in critical:
        ev.append({"name": name(f), "ph": "X", "pid": 2, "tid": 1,
                   "ts": us(start[f] - t0), "dur": us(dur[f]),
                   "args": {"seconds": round(dur[f], 2)}})
        if queued[f] > 0:
            ev.append({"name": "queued for a job", "ph": "X", "pid": 2,
                       "tid": 1, "ts": us(ready[f] - t0),
                       "dur": us(queued[f]),
                       "args": {"seconds": round(queued[f], 2)}})
    for f in ideal:
        ev.append({"name": name(f), "ph": "X", "pid": 2, "tid": 2,
                   "ts": us(finish[f] - dur[f]), "dur": us(dur[f]),
                   "args": {"seconds": round(dur[f], 2)}})

    ev += counters([(start[f], 1) for f in files] +
                   [(end[f], -1) for f in files], "compiling", t0)
    ev += counters([(ready[f], 1) for f in files] +
                   [(start[f], -1) for f in files], "queued", t0)

    with open(args.output, "w") as out:
        json.dump({"traceEvents": ev, "displayTimeUnit": "ms"}, out)

    wall, cpu = t1 - t0, sum(dur.values())
    print(f"files:         {len(files)}")
    print(f"jobs:          {max(lanes.values()) + 1}")
    print(f"wall time:     {fmt(wall)}")
    print(f"compile time:  {fmt(cpu)}  (average parallelism {cpu / wall:.2f})")
    print(f"longest chain: {fmt(bound)}  (lower bound with unlimited jobs)")
    print(f"\nslowest {args.top} files:")
    for f in sorted(files, key=dur.get, reverse=True)[:args.top]:
        print(f"  {fmt(dur[f])}  {f}")
    print("\ncritical path as built (queued: waited for a free job):")
    for f in critical:
        q = f"  queued {queued[f]:.1f}s" if queued[f] >= 0.1 else ""
        print(f"  {fmt(dur[f])}  {f}{q}")
    print("\nlongest chain with unlimited jobs:")
    for f in ideal:
        print(f"  {fmt(dur[f])}  {f}")
    print("\nlongest queued for a job:")
    for f in sorted(files, key=queued.get, reverse=True)[:args.top]:
        if queued[f] >= 0.1:
            print(f"  {fmt(queued[f])}  {f}")
    print(f"\ntrace: {args.output} (open in https://ui.perfetto.dev)")


if __name__ == "__main__":
    main()
