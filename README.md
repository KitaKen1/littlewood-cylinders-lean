# Littlewood's mutually touching cylinders problem in Lean

Littlewood's cylinder problem is the following conjecture.

> **Conjecture.** The maximum number of congruent infinite circular cylinders in
> Euclidean three-space that touch pairwise and have pairwise disjoint interiors
> is seven.

The existence of a configuration with $N=7$ is already known, by the work of
[Bozóki, Lee, and Rónyai](https://arxiv.org/abs/1308.5164). This repository answers
the conjecture affirmatively by proving that **no such configuration exists for
$N\ge8$**. The Lean development formalizes both this upper bound and the known
existence result.

The repository has three parts:

1. **[Formal Conjectures-style statement](fclikelean/LittlewoodCylinders.lean).**
   A proposed statement with all the geometry written directly in the theorem.
   This is an unofficial, unsubmitted draft; its `answer(sorry)` and `by sorry`
   are intentional statement placeholders.
2. **[Complete proof on the Formal Conjectures toolchain](lean/LittlewoodCylindersFC.lean).**
   The modular proof, checked with Lean 4.33.1, including exact certificates for
   the lower bound, the geometric upper bound, and the final axiom audit.
3. **[Standalone Lean4Web proof](lean4web/LittlewoodCylindersLean4Web.lean).**
   A single mathlib-only file containing the proof and its certificates. It was
   checked locally with Lean 4.34.1 and on public Lean4Web with Stable Lean 4.34.0.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Flittlewood-cylinders-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FLittlewoodCylindersLean4Web.lean)

The link selects the Stable mathlib project; the recorded public check used
Lean 4.34.0. To load a local copy, use **Load → Load file from disk** instead.
The file is about 10.3 MB, so processing takes time. Verification is complete when the final
`#print axioms LittlewoodCylinders.littlewood_cylinders` reports only
`[propext, Classical.choice, Quot.sound]`.

## Formal Conjectures target

The completed declaration in
[`lean/LittlewoodCylindersFC.lean`](lean/LittlewoodCylindersFC.lean) is:

```lean
theorem littlewood_cylinders : answer(True) ↔
    IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7 := by
  constructor
  · intro _
    exact maximum_seven_of seven_exists no_eight
  · intro _
    trivial
```

The declaration is in the namespace `LittlewoodCylinders`. Its components have
the following mathematical meaning:

| Lean expression | Meaning |
|---|---|
| `EuclideanSpace ℝ (Fin 3)` | Euclidean three-space, with its Euclidean metric |
| `L : Fin n → AffineSubspace ℝ …` | An indexed family of `n` affine subspaces |
| `Module.finrank ℝ (L i).direction = 1` | Each affine subspace is a line |
| `sInf {r : ℝ \| ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r}` | The distance between the two lines |
| `∀ i j, i ≠ j → … = 1` | Every two differently indexed lines are at distance one |
| `IsGreatest {n : ℕ \| …} 7` | Seven is attained and bounds every possible size |
| `answer(True)` | The affirmative answer in Formal Conjectures notation |

Distinct indices necessarily give distinct lines: a line's distance from itself
is zero. The proof establishes nonemptiness and the lower bound needed for the
distance infimum. Helper definitions are used internally, and
`inline_statement_iff_helper` proves their equivalence to this fully inlined
statement.

The [statement draft](fclikelean/README.md) is provided for preparing a Formal
Conjectures contribution. It has not been submitted or accepted.

## Mathematical explanation (AI generated)

### 1. Certify seven lines exactly

The lower bound starts from a polynomial system describing seven mutually
touching axes. Rational data specify an approximate solution, a surrounding
closed cube, and a preconditioner. The proof checks bounds showing that an
associated map preserves this cube and is a contraction.

The fixed-point theorem therefore gives an exact real solution. Invertibility
of the preconditioner turns the fixed-point equations into the original
polynomial equations. Additional direction certificates exclude degenerate
axes. The resulting lines are rescaled to have pairwise distance one.

Thus the existence proof obtains actual real lines from checked rational
bounds. Its endpoint is
`LowerCertificate.exists_seven_affine_lines`, used by `seven_exists`.

### 2. Turn eight hypothetical lines into sign data

For the upper bound, assume that eight affine lines have pairwise distance one.
The geometric part proves that no pair is parallel and that every triple of
direction vectors is linearly independent.

Write a line as $p_i + \mathbb{R}u_i$. For nonparallel lines, the distance formula
is

$$
\operatorname{dist}(L_i,L_j)
= \frac{|(p_j-p_i)\cdot(u_i\times u_j)|}{\|u_i\times u_j\|}.
$$

This formula supplies symmetric contact signs $E_{ij}\in\{-1,1\}$ for distinct
indices. Determinants of triples of directions supply orientation signs
$\chi_{ijk}\in\{-1,1\}$ for distinct triples. Geometric identities and norm
inequalities force these signs to satisfy Grassmann–Plücker, tetrahedron,
closed-polygon, and five-direction constraints.

Relabeling and reorienting the axes, together with the proved global sign
symmetries, preserve realizability. These symmetries allow the normalization
$E_{0i}=1$ for $i\ne0$ and $\chi_{012}=1$. The remaining contact signs can then
be represented by a graph on seven labels.

### 3. Exclude a five-label pattern by parity

Suppose that five labels have contact signs of the form
$E_{ij}=g f_i f_j$, where $g$ and the $f_i$ are signs. The tetrahedron condition
gives an equation for each of the five four-label subsets.

Multiply those five equations. Each label sign occurs four times and each
triple-orientation sign occurs twice, so the left side is $1$. The right side
is $(-1)^5=-1$. This contradiction excludes the pattern.

This is the theorem `signed_five_impossible` in
[`UpperFiveParity.lean`](lean/UpperFiveParity.lean). The absence of the forbidden
pattern is preserved when vertices are deleted, which allows it to be used
while building the graph cover.

### 4. Prove a complete finite cover

The graph cover is built inductively. For every extension, Lean checks either
an explicit isomorphism to a retained representative or a five-label witness
that excludes it. The induction proves that every graph arising from the
hypothetical geometry is covered.

There are 5,115 checked extension certificates and 202 retained seven-vertex
representatives. Checked signed permutations map these representatives into
31 members of the stored array of 131 contact matrices. The array is retained
as the common interface to the exclusion proofs.

The search program supplies witnesses; the Lean proof establishes their
validity and the coverage theorem. Completeness is not assumed from the
program's output.

### 5. Refute the remaining sign systems

For each contact matrix, necessary sign conditions are expressed as Boolean
clauses. The theorem `Reason.sound` proves that a realizable configuration
satisfies each clause justified by one of the geometric constraints.

The modular proof checks LRAT refutations for all 131 stored cases. LRAT is a
proof-certificate format for propositional unsatisfiability; here each checked
refutation is reconstructed as a Lean proof term. The SAT solver's answer is
not a new axiom.

The standalone export uses the short five-label parity proof for 100 cases
and retains LRAT proofs for the remaining 31. Together with the coverage
theorem, these exclusions prove `no_eight`.

### 6. Assemble the greatest-cardinality theorem

Finally, `maximum_seven_of seven_exists no_eight` combines the exact lower bound
with the upper bound. Restriction to eight members excludes every larger
finite family. The final theorem above is short because its geometric and
finite-certificate arguments have already been proved in separate components.

## Scope

The formal theorem concerns affine lines in Euclidean three-space and their
distance infima. The interpretation as congruent infinite circular cylinders
uses the usual geometric correspondence between a cylinder and its axis; the
repository does not separately formalize cylinder surfaces or solid-cylinder
topology.

The theorem has no generic-position hypothesis. The nondegeneracy needed by
the sign argument is proved from the hypothetical eight-line configuration.
It also has no assumption that a finite table is complete: graph coverage and
the soundness of the obstruction clauses are part of the Lean proof.

An earlier collection of 827 recorded orientation cases remains in the
modular development. Its local obstructions are checked, but the final upper
bound does not require that collection to enumerate all orientation orbits.

The completed affine-line theorem has passed Lean's kernel checks.

## Files

| Directory | Environment | Contents |
|---|---|---|
| [`fclikelean/`](fclikelean/README.md) | Formal Conjectures-style draft | Inlined conjecture statement; intentional placeholders |
| [`lean/`](lean/README.md) | Lean 4.33.1; pinned Formal Conjectures dependency | Modular proof and certificate data |
| [`lean4web/`](lean4web/README.md) | Lean 4.34.1; pinned mathlib dependency | Complete standalone proof and build configuration |

The modular proof can be read in dependency order:

| Part | Main files |
|---|---|
| Exact lower-bound certificate | [`LowerCertificateSoundness.lean`](lean/LowerCertificateSoundness.lean), [`LowerSolution.lean`](lean/LowerSolution.lean) |
| Construction of the seven axes | [`DirectionCertificate.lean`](lean/DirectionCertificate.lean), [`RootLines.lean`](lean/RootLines.lean) |
| Distances and nondegeneracy | [`UpperDistance.lean`](lean/UpperDistance.lean), [`UpperNondegenerate.lean`](lean/UpperNondegenerate.lean), [`UpperNoParallel.lean`](lean/UpperNoParallel.lean) |
| Necessary signs and normalization | [`UpperNecessarySigns.lean`](lean/UpperNecessarySigns.lean), [`UpperSignNormalization.lean`](lean/UpperSignNormalization.lean) |
| Parity obstruction and graph cover | [`UpperFiveParity.lean`](lean/UpperFiveParity.lean), [`UpperPrunedGraphCover.lean`](lean/UpperPrunedGraphCover.lean), [`UpperContactCoverage.lean`](lean/UpperContactCoverage.lean) |
| Clause soundness and finite refutations | [`UpperSATClauses.lean`](lean/UpperSATClauses.lean), [`UpperLRAT.lean`](lean/UpperLRAT.lean), [`UpperSATCoverage.lean`](lean/UpperSATCoverage.lean) |
| Final theorem and audit entry points | [`LittlewoodCylindersFC.lean`](lean/LittlewoodCylindersFC.lean), [`LittlewoodVerified.lean`](lean/LittlewoodVerified.lean) |

Exact dependency revisions are recorded in the
[modular Lake configuration](lean/lakefile.toml) and
[standalone Lake configuration](lean4web/lakefile.toml).

## Verification

From the repository root, build the modular proof with its pinned toolchain:

```bash
cd lean
lake update
lake exe cache get
lake --wfail build
```

Alternatively, from the repository root, check the standalone file:

```bash
cd lean4web
lake update
lake exe cache get
lake env lean -j1 LittlewoodCylindersLean4Web.lean
```

The final axiom report is:

```text
'LittlewoodCylinders.littlewood_cylinders' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are the three standard axioms used by the completed theorem. Its
dependency audit contains no `sorryAx` or project-specific axiom. The
intentional placeholders in `fclikelean/` belong only to the statement draft.

## Sources

- Sándor Bozóki, Tsung-Lin Lee, and Lajos Rónyai,
  [*Seven mutually touching infinite cylinders*](https://arxiv.org/abs/1308.5164),
  arXiv:1308.5164; *Computational Geometry* 48(2) (2015), 87–93.
- Junnosuke Koizumi,
  [*A new upper bound for mutually touching infinite cylinders*](https://arxiv.org/abs/2506.19309),
  arXiv:2506.19309 (2025).
- Travis Dillon, Junnosuke Koizumi, and Sammy Luo,
  [*At most 10 cylinders mutually touch: a Ramsey-theoretic approach*](https://arxiv.org/abs/2510.03924),
  arXiv:2510.03924 (2025).
- Jozsef Solymosi and Josh Zahl,
  [*On the number of pairwise touching cylinders in $\mathbb{R}^d$*](https://arxiv.org/abs/2512.24595),
  arXiv:2512.24595 (2025).
- Roland Höfer,
  [*At most nine lines in Euclidean three-space have pairwise distance one*](https://arxiv.org/abs/2606.22605),
  arXiv:2606.22605 (2026).
- The three-directory layout and the presentation of this README follow
  [`KitaKen1/kourovka-21-149-lean`](https://github.com/KitaKen1/kourovka-21-149-lean).

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code using Claude Opus 5.5.

## Appendix: history of the problem

Let $N$ denote the maximum size of a family of mutually touching congruent
infinite circular cylinders with disjoint interiors.
[Bozóki, Lee, and Rónyai](https://arxiv.org/abs/1308.5164) established the existence
of seven cylinders in a 2013 preprint, published in 2015, giving $N\ge7$.

The subsequent upper-bound results and a higher-dimensional generalization are
listed below. Dates refer to the first arXiv submission, not journal publication.

| Date | Authors | Bound | Method and scope |
|---|---|---|---|
| 2025-06-24 | [Junnosuke Koizumi](https://arxiv.org/abs/2506.19309) | $N\le18$ | Pairwise chirality signs form a signed graph; a forbidden monochromatic five-vertex clique and Ramsey theory improve the previous bound of 24 |
| 2025-10-04 | [Travis Dillon, Junnosuke Koizumi, Sammy Luo](https://arxiv.org/abs/2510.03924) | $N\le10$; $N\le12$ without computer assistance | Linear algebra and Ramsey theory, with partial computer verification for the bound of 10 |
| 2025-12-31 | [Jozsef Solymosi, Josh Zahl](https://arxiv.org/abs/2512.24595) | Higher-dimensional bounds | Generalization to $\mathbb{R}^d$, with upper bounds exponential in $d$, using polynomial equalities and non-equalities to express touching |
| 2026-06-21 | [Roland Höfer](https://arxiv.org/abs/2606.22605) | $N\le9$ | A computer-free linear-algebra proof using Veronese–Plücker coordinates and a bilinear form |

Thus these cited three-dimensional results give the progression
$24\to18\to10\to9$ for the upper bound. The higher-dimensional paper is a
separate generalization in this timeline.

Together, the seven-cylinder construction and Höfer's bound leave
$7\le N\le9$ in the cited literature. An upper bound of nine excludes ten or
more cylinders; it does not exclude configurations of eight or nine. Excluding
eight would also exclude nine, since any nine-member configuration contains an
eight-member subconfiguration.

The theorem in this repository proves exact existence for seven affine axes
and excludes an arbitrary hypothetical eight-axis configuration. Its formal
upper bound is established by the geometric and finite-sign arguments above,
without assuming a published exclusion of nine or more cylinders.
