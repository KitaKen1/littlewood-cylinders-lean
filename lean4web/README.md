# Standalone Lean4Web proof

[`LittlewoodCylindersLean4Web.lean`](LittlewoodCylindersLean4Web.lean) contains
the complete proof of the final affine-line theorem, including its certificate
data. It needs mathlib, with no project-specific imports or external proof files.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Flittlewood-cylinders-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FLittlewoodCylindersLean4Web.lean)

The file was checked locally with Lean **4.34.1** and on public Lean4Web with
Stable Lean **4.34.0**. Wait for processing to reach the final axiom report:

```text
'LittlewoodCylinders.littlewood_cylinders' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

To load a local copy, select the Stable mathlib project and use
**Load → Load file from disk**.

## Local check

Run from this directory:

```bash
lake update
lake exe cache get
lake env lean -j1 LittlewoodCylindersLean4Web.lean
```

The toolchain and mathlib revision are pinned in
[`lean-toolchain`](lean-toolchain) and [`lakefile.toml`](lakefile.toml).
See the [main README](../README.md) for the mathematical explanation and the
[modular proof](../lean/README.md) for the source modules.
