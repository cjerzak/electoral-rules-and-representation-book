# Setup instructions

```markdown
# Lean/Mathlib Setup Instructions

## Reusable Future Setup Pattern

For a reusable future setup, use this pattern:

### One-time setup
```bash
mkdir -p "$HOME/lean-envs/mathlib-v4.31.0"
cd "$HOME/lean-envs/mathlib-v4.31.0"
~/.elan/bin/lake init MathlibEnv math-lax
~/.elan/bin/lake build Mathlib
```

### Recompile the proof file
```bash
cd "$HOME/lean-envs/mathlib-v4.31.0"
~/.elan/bin/lake env lean "/Users/cjerzak/Library/CloudStorage/Dropbox/GLP/Electoral systems/ProofChecks/descriptive_representation_formal_theorems.lean"
```

---

## Immediate Shortcut (using the already-created temp Mathlib project)

```bash
cd /tmp/sketchqr-lean-check.hfaNXP
~/.elan/bin/lake env lean "/Users/cjerzak/Library/CloudStorage/Dropbox/GLP/Electoral systems/ProofChecks/descriptive_representation_formal_theorems.lean"
```
```

Copy the block above into a `.md` file (or paste directly into any Markdown-supported editor/Notion/Obsidian/etc.) for clean, ready-to-use formatting. Let me know if you'd like a version with extra explanations, numbered steps, or collapsed sections!


