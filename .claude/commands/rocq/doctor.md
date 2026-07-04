---
name: doctor
description: Diagnostics, cleanup, and migration help
user_invocable: true
---

# Rocq Doctor

Diagnostics, troubleshooting, and environment checking for the Rocq plugin.

## Usage

```
/rocq:doctor                    # Full diagnostic (plugin + workspace)
/rocq:doctor env                # Environment only
/rocq:doctor cleanup            # Show stale files + removal commands
/rocq:doctor cleanup --apply    # Actually remove stale files
```

## Inputs

| Arg | Required | Description |
|-----|----------|-------------|
| mode | No | `env`, `cleanup`, or full (default) |
| --apply | No | Execute removals; cleanup only |

## Actions

### 1. Environment Check

| Tool | Check | Required |
|------|-------|----------|
| `coqc` | `coqc --version` | Yes |
| `coq_makefile` | `coq_makefile --version` | For project builds |
| `python3` | `python3 --version` | For scripts |
| `git` | `git --version` | For commits |
| `rg` | `rg --version` | Optional (faster search) |

Environment variables: `ROCQ_PLUGIN_ROOT`, `ROCQ_SCRIPTS`, `ROCQ_REFS`, `ROCQ_PYTHON_BIN`

### 1b. MCP Tools

| Check | Detection | Status |
|-------|-----------|--------|
| Rocq MCP | `rocq_query("Check nat.")` available | Optional (interactive proving) |
| Rocq MCP version | `uvx --version rocq-mcp` vs PyPI latest (`pip index versions rocq-mcp 2>/dev/null \|\| curl -s https://pypi.org/pypi/rocq-mcp/json \| python3 -c "import sys,json; print(json.load(sys.stdin)['info']['version'])"`) | Warn if outdated |

If the installed version is behind the latest PyPI release, print a warning with the upgrade command:
```
⚠ rocq-mcp vX.Y.Z installed — latest is vA.B.C
  Upgrade: claude mcp remove rocq-mcp && claude mcp add --transport stdio --scope user rocq-mcp -- uvx rocq-mcp@latest
```

### 2. Plugin Check

Verify structure and permissions:
```
plugins/rocq/
├── .claude-plugin/plugin.json
├── commands/     (*.md command files)
├── hooks/        (executable .sh)
├── skills/rocq/  (SKILL.md + references/)
├── agents/       (4 files)
└── lib/scripts/  (executable)
```

### 3. Project Check

- `_CoqProject` or `CoqMakefile` present
- Project build passes (`make` or `coqc`)
- Admitted count reported

### 4. Cleanup

Detects and optionally removes obsolete artifacts.

**Behavior:**
- Default: Report findings, show `rm -rf` commands, do NOT execute
- With `--apply`: Interactive per-item confirmation

## Output

**Full diagnostic:**
```markdown
## Rocq Doctor Report

### Environment
coqc 8.x.x
python3 3.x.x
...

### MCP Tools
Rocq MCP tools available (rocq_query)
rocq-mcp up to date | ⚠ rocq-mcp outdated (vX.Y.Z → vA.B.C)

### Plugin
ROCQ_PLUGIN_ROOT set
Scripts executable
...

### Project
Build passes
N Admitted in M files

### Status: Ready
```

## Troubleshooting

| Issue | Fix |
|-------|-----|
| ROCQ_SCRIPTS not set | Restart session, check hooks.json |
| coqc not found | Install via opam (`opam install coq`) |
| Scripts not executable | `chmod +x $ROCQ_SCRIPTS/*.sh` |
| Build fails | Check `_CoqProject`, run `coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile` |
| Rocq MCP tools unavailable | Check `claude mcp list`; if missing, `claude mcp add --transport stdio --scope user rocq-mcp -- uvx rocq-mcp` |
| Rocq MCP outdated | `claude mcp remove rocq-mcp && claude mcp add --transport stdio --scope user rocq-mcp -- uvx rocq-mcp@latest` |

## Safety

- All modes are read-only by default
- `cleanup` shows commands but does not execute without `--apply`
- `cleanup --apply` prompts per-item
- Does not modify Rocq source files

## See Also

- `/rocq:prove` - Guided cycle-by-cycle proving
- `/rocq:checkpoint` - Save progress
