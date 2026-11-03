"""Sum Claude Code token usage over a project's session transcripts.

Usage: python3 -I .claude/tools/transcript-usage.py ~/.claude/projects/-home-emiel-Documents-katamaran

Per session (main + its subagents/): requests, cache reads/writes, output, an
input-equivalent WEIGHTED total (cache read 0.1, 5-min write 1.25, 1-h write 2,
output 5 -- list-price ratios), first-request context, compactions; then tool
result volume by tool. Assistant records are DEDUPED by message.id (one API
response is logged once per content block).

Caveats found when this was first run (2026-11-03, PLAN-context-economy):
- Read's character count includes base64 images (poster PNGs): characters are
  not tokens for those. Split images out before quoting Read's share.
- Transcripts older than ~30 days are deleted by Claude Code; the July 2026
  incidents are not measurable from here.
Local only: reads files, makes no API calls.
"""
import json, sys, glob, os, collections

root = sys.argv[1]
# Relative price weights vs base input (Anthropic list-price ratios):
W = dict(inp=1.0, cw5=1.25, cw1h=2.0, cr=0.1, out=5.0)

def load(path):
    msgs = {}            # message.id -> usage (dedupe streamed blocks)
    first_ctx = None
    tool_names = {}      # tool_use_id -> name
    tool_chars = collections.Counter()
    tool_calls = collections.Counter()
    compacts = 0
    t0 = t1 = None
    model = collections.Counter()
    for line in open(path, errors='replace'):
        try:
            d = json.loads(line)
        except Exception:
            continue
        ts = d.get('timestamp')
        if ts:
            t0 = t0 or ts
            t1 = ts
        if d.get('type') == 'system' and d.get('subtype') == 'compact_boundary':
            compacts += 1
        m = d.get('message')
        if not isinstance(m, dict):
            continue
        if d.get('type') == 'assistant':
            u = m.get('usage')
            mid = m.get('id')
            if u and mid:
                msgs[mid] = (u, m.get('model'))
                if first_ctx is None:
                    first_ctx = u.get('input_tokens', 0) + u.get('cache_creation_input_tokens', 0) + u.get('cache_read_input_tokens', 0)
            for c in m.get('content') or []:
                if isinstance(c, dict) and c.get('type') == 'tool_use':
                    tool_names[c['id']] = c.get('name')
        elif d.get('type') == 'user':
            for c in m.get('content') or [] if isinstance(m.get('content'), list) else []:
                if isinstance(c, dict) and c.get('type') == 'tool_result':
                    name = tool_names.get(c.get('tool_use_id'), '?')
                    cont = c.get('content')
                    n = len(cont) if isinstance(cont, str) else len(json.dumps(cont))
                    tool_chars[name] += n
                    tool_calls[name] += 1
    tot = collections.Counter()
    for u, mod in msgs.values():
        cc = u.get('cache_creation') or {}
        cw1h = cc.get('ephemeral_1h_input_tokens', 0)
        cw5 = cc.get('ephemeral_5m_input_tokens', u.get('cache_creation_input_tokens', 0) - cw1h)
        tot['inp'] += u.get('input_tokens', 0)
        tot['cw5'] += cw5
        tot['cw1h'] += cw1h
        tot['cr'] += u.get('cache_read_input_tokens', 0)
        tot['out'] += u.get('output_tokens', 0)
        tot['req'] += 1
        model[mod] += 1
    tot['weighted'] = sum(tot[k] * W[k] for k in W)
    return dict(tot=tot, first_ctx=first_ctx, tool_chars=tool_chars, tool_calls=tool_calls,
                compacts=compacts, t0=t0, t1=t1, model=model)

sessions = {}
for p in glob.glob(os.path.join(root, '*.jsonl')):
    sid = os.path.basename(p)[:-6]
    main = load(p)
    subs = [load(s) for s in glob.glob(os.path.join(root, sid, 'subagents', '*.jsonl'))]
    sessions[sid] = (main, subs)

def M(x): return f"{x/1e6:8.2f}M"

grand = collections.Counter(); grand_sub = collections.Counter()
tools = collections.Counter(); toolcalls = collections.Counter()
models = collections.Counter()
rows = []
for sid, (mn, subs) in sessions.items():
    sub = collections.Counter()
    for s in subs:
        sub.update(s['tot']); models.update(s['model'])
    grand.update(mn['tot']); grand_sub.update(sub); models.update(mn['model'])
    tools.update(mn['tool_chars']); toolcalls.update(mn['tool_calls'])
    rows.append((mn['tot']['weighted'] + sub['weighted'], sid, mn, sub, len(subs)))

print("GRAND (main sessions):")
for k in ['req', 'inp', 'cw5', 'cw1h', 'cr', 'out', 'weighted']:
    print(f"  {k:9s} {M(grand[k])}   subagents {M(grand_sub[k])}")
print("models (requests):", dict(models))
tw = grand['weighted'] + grand_sub['weighted']
print("\nshare of weighted cost by component (main+sub):")
for k in W:
    v = (grand[k] + grand_sub[k]) * W[k]
    print(f"  {k:5s} {100*v/tw:5.1f}%")
print(f"  subagents total {100*grand_sub['weighted']/tw:5.1f}%")

print("\nper session, by weighted cost:")
print("  weighted   reqs  cacheRead   output  firstCtx compacts subs  dates                      sid")
for w, sid, mn, sub, ns in sorted(rows, reverse=True):
    t = mn['tot']
    print(f"  {M(w)} {t['req']:5d} {M(t['cr'])} {M(t['out'])} {mn['first_ctx'] or 0:8d} {mn['compacts']:5d} {ns:4d}  {(mn['t0'] or '')[:10]}..{(mn['t1'] or '')[:10]}  {sid[:8]}  sub={M(sub['weighted'])}")

firsts = sorted(mn['first_ctx'] for mn, _ in sessions.values() if mn['first_ctx'])
print("\nfirst-request context (tokens): min", firsts[0], "median", firsts[len(firsts)//2], "max", firsts[-1])

print("\ntool-result volume in main sessions (chars, ~tokens = chars/4):")
totc = sum(tools.values())
for name, c in tools.most_common(15):
    print(f"  {name:45s} {c/1e6:7.2f}M chars {100*c/totc:5.1f}%  calls {toolcalls[name]:6d}  avg {c//max(1,toolcalls[name]):6d}")
