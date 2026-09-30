# Modular Lean proof

[`LittlewoodCylindersFC.lean`](LittlewoodCylindersFC.lean) proves the fully
inlined greatest-cardinality theorem: seven affine lines at pairwise distance
one exist in Euclidean three-space, and eight or more cannot exist.

The proof was checked with Lean **4.33.1** and the Formal Conjectures revision
pinned in [`lakefile.toml`](lakefile.toml).

## Proof structure

| Part | Entry point |
|---|---|
| Exact seven-line existence certificate | [`RootLines.lean`](RootLines.lean) |
| Geometric reduction and complete contact-matrix coverage | [`UpperContactCoverage.lean`](UpperContactCoverage.lean) |
| Checked finite refutations and the upper bound | [`UpperSATCoverage.lean`](UpperSATCoverage.lean) |
| Final theorem | [`LittlewoodCylindersFC.lean`](LittlewoodCylindersFC.lean) |
| Component axiom audit | [`LittlewoodVerified.lean`](LittlewoodVerified.lean) |

The certificate data are included in the Lean sources. Building the proof does
not require Python, an external SAT solver, or the original search programs.
The geometric reduction and completeness of the finite cover are proved in Lean.

## Build

Run from this directory:

```bash
lake update
lake exe cache get
lake --wfail build
```

The final axiom report is:

```text
'LittlewoodCylinders.littlewood_cylinders' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The completed proof has no `sorry`. The separate
[`fclikelean/`](../fclikelean/README.md) directory contains the statement draft.
See the [main README](../README.md) for the mathematical explanation and the
[standalone version](../lean4web/README.md) for Lean4Web.
