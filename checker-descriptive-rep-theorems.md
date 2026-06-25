# Lean/Mathlib Setup and Proof-Checking Instructions

This note explains how to set up Lean 4 with Mathlib and how to check the accompanying formal proof file:

```text
descriptive_representation_formal_theorems.lean
```

The commands below are intended to be portable across machines. Replace file paths such as `/path/to/...` with the actual location of the proof file on your own computer.

## 1. Install Lean

Lean 4 is usually installed through `elan`, the Lean toolchain manager. The easiest route is to install the official Lean 4 extension in VS Code and follow its setup guide. This installs or configures the needed Lean tooling, including `elan`, `lean`, and `lake`.

After installation, open a terminal and check that the tools are available:

```bash
elan --version
lean --version
lake --version
```

If these commands fail, restart the terminal or confirm that the Lean/elan binaries are on your shell path.

## 2. Create a Mathlib Project

The proof file uses Mathlib, so it should be checked from inside a Lean project that depends on Mathlib.

Choose a convenient location for Lean projects, then create a new Mathlib-based project:

```bash
mkdir -p "$HOME/lean-envs"
cd "$HOME/lean-envs"

lake +leanprover-community/mathlib4:lean-toolchain new descriptive-representation-check math
cd descriptive-representation-check
```

This creates a new Lean project with Mathlib as a dependency.

## 3. Download or Build Mathlib Dependencies

From inside the project directory, run:

```bash
lake update
lake exe cache get
lake build
```

The cache command downloads precompiled Mathlib files when available, which is usually much faster than compiling all of Mathlib locally.

## 4. Check the Proof File

Once the project is set up, run Lean on the proof file from inside the project directory.

Generic form:

```bash
cd "$HOME/lean-envs/descriptive-representation-check"
lake env lean "/path/to/descriptive_representation_formal_theorems.lean"
```

For Connor Jerzak’s local machine, the command may look like:

```bash
cd "$HOME/lean-envs/descriptive-representation-check"
lake env lean "/Users/cjerzak/Library/CloudStorage/Dropbox/GLP/Electoral systems/ProofChecks/descriptive_representation_formal_theorems.lean"
```

Users on other machines should replace the path after `lake env lean` with the location of the `.lean` file on their own system.

## 5. What Success Looks Like

If the file checks successfully, Lean may print little or no output. The key sign of success is that the command exits without an error.

If there is an error, Lean will print a message identifying the file location and the theorem, definition, import, or tactic that failed.

## 6. Optional: Temporary Existing Project Shortcut

If a Mathlib project has already been created elsewhere, it is also possible to check the file from that existing project. For example, on one machine the project was located at:

```bash
cd /tmp/sketchqr-lean-check.hfaNXP
lake env lean "/Users/cjerzak/Library/CloudStorage/Dropbox/GLP/Electoral systems/ProofChecks/descriptive_representation_formal_theorems.lean"
```

This shortcut is machine-specific and should not be used as the primary reproducibility instruction. It is included only as an example of the general pattern:

```bash
cd /path/to/any/working/mathlib/project
lake env lean /path/to/the/proof/file.lean
```

## 7. Troubleshooting

If Lean cannot find Mathlib, make sure the command is being run from inside a Mathlib-based project and that `lake update` and `lake build` have completed.

If the proof file imports modules that are unavailable, the local Mathlib version may be different from the one used when the file was written. In that case, update the project, or pin the project to the Lean/Mathlib version used by the authors.

If a file path contains spaces, wrap it in quotation marks, as in:

```bash
lake env lean "/Users/name/path with spaces/descriptive_representation_formal_theorems.lean"
```
