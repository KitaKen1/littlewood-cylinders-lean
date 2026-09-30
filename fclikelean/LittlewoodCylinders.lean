/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Littlewood's mutually touching infinite cylinders problem

Is seven the maximum number of congruent infinite circular cylinders in Euclidean
three-space such that every two cylinders touch and their interiors are disjoint?

After scaling the common radius to `1 / 2`, the problem is equivalent to asking for
the greatest number of affine lines in Euclidean three-space whose pairwise distances
are one.

*References:*
- [S. Bozóki, T.-L. Lee and L. Rónyai, *Seven mutually touching infinite cylinders*]
  (https://arxiv.org/abs/1308.5164)
- [J. Koizumi, *A new upper bound for mutually touching infinite cylinders*]
  (https://arxiv.org/abs/2506.19309)
-/

@[expose] public section

namespace LittlewoodCylinders

/--
Is seven the greatest number of affine lines in Euclidean three-space whose pairwise
distances are exactly one? This is the normalized form of Littlewood's problem on
mutually touching congruent infinite circular cylinders.
-/
@[category research open, AMS 51 52]
theorem littlewood_cylinders : answer(sorry) ↔
    IsGreatest
      {n : ℕ |
        ∃ L : Fin n → AffineSubspace ℝ
            (EuclideanSpace ℝ (Fin 3)),
          (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
          ∀ i j, i ≠ j →
            sInf {r : ℝ |
              ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1}
      7 := by
  sorry

end LittlewoodCylinders
