import Mathlib
import DirectionCertificate
import LineGeometry

namespace LittlewoodCylinders.LowerCertificate

open scoped RealInnerProductSpace
open LowerCertificateData
open LittlewoodCylinders.LineGeometry

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev toE3 (a : RVec3) : E3 := WithLp.toLp 2 a

noncomputable abbrev halfVec (a : RVec3) : RVec3 := fun q => a q / 2

lemma inner_toE3 (a b : RVec3) : ⟪toE3 a, toE3 b⟫ = dotR a b := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, dotR, Fin.sum_univ_succ]
  ring

lemma norm_toE3_sq (a : RVec3) : ‖toE3 a‖ ^ 2 = dotR a a := by
  rw [← real_inner_self_eq_norm_sq, inner_toE3]

lemma cross_left_orthogonal (u v : RVec3) : dotR u (crossR u v) = 0 := by
  simp [dotR, crossR]
  ring

lemma cross_right_orthogonal (u v : RVec3) : dotR v (crossR u v) = 0 := by
  simp [dotR, crossR]
  ring

lemma cross_norm_identity (u v : RVec3) :
    dotR (crossR u v) (crossR u v) =
      dotR u u * dotR v v - dotR u v * dotR u v := by
  simp [dotR, crossR]
  ring

lemma closest_displacement_aux (p q u v : RVec3) (D : ℝ)
    (hD : D ≠ 0) (hDdef : D = dotR (crossR u v) (crossR u v)) :
    let d := vsubR q p
    let n := crossR u v
    let a := dotR u u
    let b := dotR u v
    let c := dotR v v
    let s := (c * dotR d u - b * dotR d v) / (2 * D)
    let t := (b * dotR d u - a * dotR d v) / (2 * D)
    (fun k => q k / 2 + t * v k - (p k / 2 + s * u k)) =
      fun k => (dotR d n / (2 * D)) * n k := by
  dsimp only
  funext k
  field_simp [hD]
  rw [hDdef]
  fin_cases k <;> simp [crossR, dotR] <;> ring

lemma closest_displacement (p q u v : RVec3)
    (hD : dotR (crossR u v) (crossR u v) ≠ 0) :
    let d := vsubR q p
    let n := crossR u v
    let D := dotR n n
    let a := dotR u u
    let b := dotR u v
    let c := dotR v v
    let s := (c * dotR d u - b * dotR d v) / (2 * D)
    let t := (b * dotR d u - a * dotR d v) / (2 * D)
    (fun k => q k / 2 + t * v k - (p k / 2 + s * u k)) =
      fun k => (dotR d n / (2 * D)) * n k := by
  exact closest_displacement_aux p q u v
    (dotR (crossR u v) (crossR u v)) hD rfl

lemma direction_ne_zero (x : V) (i : Fin 7) : directionsR x i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  fin_cases i <;> simp [directionsR, vec3R] at h0 h1 h2 <;> linarith

lemma distance_equation_of_root {x : V}
    (hroot : ∀ k, distanceSystemR x k = 0)
    {i j : Fin 7} (hij : i < j) :
    let p := pointsR x i
    let q := pointsR x j
    let u := directionsR x i
    let v := directionsR x j
    let n := crossR u v
    let triple := dotR (vsubR q p) n
    triple ^ 2 = 4 * dotR n n := by
  dsimp only
  by_cases h01 : (i, j) = ((0 : Fin 7), (1 : Fin 7))
  · rcases Prod.ext_iff.mp h01 with ⟨rfl, rfl⟩
    norm_num [pointsR, directionsR, vec3R, vsubR, crossR, dotR, Matrix.cons_val_two]
  · obtain ⟨k, hk⟩ := pairIndex_complete i j hij h01
    have hkroot := hroot k
    simp only [distanceSystemR] at hkroot
    rw [hk] at hkroot
    nlinarith

lemma pair_geometry {x : V}
    (hroot : ∀ k, distanceSystemR x k = 0)
    (hbox : ∀ i, |x i - (center i : ℝ)| ≤ (radius : ℝ))
    {i j : Fin 7} (hij : i < j) :
    lineDistance (toE3 (halfVec (pointsR x i))) (toE3 (directionsR x i))
      (toE3 (halfVec (pointsR x j))) (toE3 (directionsR x j)) = 1 := by
  let p := pointsR x i
  let q := pointsR x j
  let u := directionsR x i
  let v := directionsR x j
  let n := crossR u v
  let D := dotR n n
  let triple := dotR (vsubR q p) n
  have hz : ∀ k, |((x k - (center k : ℝ)) / (radius : ℝ))| ≤ 1 := by
    intro k
    rw [abs_div]
    have hr : |(radius : ℝ)| = (radius : ℝ) := abs_of_pos (by norm_num [radius])
    rw [hr]
    apply (div_le_iff₀' (by norm_num [radius])).2
    simpa using hbox k
  let z : V := fun k => (x k - (center k : ℝ)) / (radius : ℝ)
  have hxactual : actualVariables z = x := by
    funext k
    simp only [actualVariables, z]
    field_simp [radius_ne_zero_real]
    ring
  have hzbox : z ∈ unitCube := mem_unitCube_iff.mpr hz
  have hD : 0 < D := by
    have hp := direction_cross_norm_pos hzbox hij
    simpa [D, hxactual, u, v, n] using hp
  have heq : triple ^ 2 = 4 * D := by
    simpa [p, q, u, v, n, D, triple] using distance_equation_of_root hroot hij
  have hnSq : ‖toE3 n‖ ^ 2 = D := by simpa [D] using norm_toE3_sq n
  have hnpos : 0 < ‖toE3 n‖ := by nlinarith [norm_nonneg (toE3 n)]
  have habsTriple : |triple| = 2 * ‖toE3 n‖ := by
    apply (sq_eq_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mp
    rw [sq_abs]
    nlinarith
  have hun : ⟪toE3 u, toE3 n⟫ = 0 := by
    rw [inner_toE3]
    exact cross_left_orthogonal u v
  have hvn : ⟪toE3 v, toE3 n⟫ = 0 := by
    rw [inner_toE3]
    exact cross_right_orthogonal u v
  have hsep :
      |⟪toE3 (halfVec q) - toE3 (halfVec p), toE3 n⟫| = ‖toE3 n‖ := by
    rw [inner_sub_left, inner_toE3, inner_toE3]
    have hdot : dotR (fun k => q k / 2) n - dotR (fun k => p k / 2) n =
        triple / 2 := by
      simp [dotR]
      ring
    rw [hdot, abs_div, habsTriple]
    norm_num
  refine lineDistance_eq_one hnpos hun hvn hsep ?_
  let a := dotR u u
  let b := dotR u v
  let c := dotR v v
  let d := vsubR q p
  let s := (c * dotR d u - b * dotR d v) / (2 * D)
  let t := (b * dotR d u - a * dotR d v) / (2 * D)
  let xp : E3 := toE3 (halfVec p) + s • toE3 u
  let yq : E3 := toE3 (halfVec q) + t • toE3 v
  refine ⟨xp, mem_affineLine_iff.mpr ⟨s, rfl⟩,
    yq, mem_affineLine_iff.mpr ⟨t, rfl⟩, ?_⟩
  have hdisp := closest_displacement p q u v hD.ne'
  have hyx : yq - xp = (triple / (2 * D)) • toE3 n := by
    change toE3 (halfVec q) + t • toE3 v -
      (toE3 (halfVec p) + s • toE3 u) = _
    apply WithLp.ofLp_injective 2
    change (fun k => q k / 2 + t * v k - (p k / 2 + s * u k)) =
      fun k => (triple / (2 * D)) * n k
    simpa only [s, t, a, b, c, d, n, D, triple] using hdisp
  rw [dist_eq_norm, ← norm_neg (xp - yq), neg_sub, hyx, norm_smul, Real.norm_eq_abs]
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) hD), habsTriple]
  rw [← hnSq, pow_two]
  field_simp [hnpos.ne']

noncomputable def rootLine (x : V) (i : Fin 7) : AffineSubspace ℝ E3 :=
  affineLine (toE3 (halfVec (pointsR x i))) (toE3 (directionsR x i))

lemma rootLine_dimension (x : V) (i : Fin 7) :
    Module.finrank ℝ (rootLine x i).direction = 1 := by
  apply finrank_direction_affineLine
  intro hzero
  apply direction_ne_zero x i
  apply WithLp.toLp_injective 2
  simpa [toE3] using hzero

lemma rootLine_distance {x : V}
    (hroot : ∀ k, distanceSystemR x k = 0)
    (hbox : ∀ i, |x i - (center i : ℝ)| ≤ (radius : ℝ))
    {i j : Fin 7} (hij : i ≠ j) :
    sInf {r : ℝ | ∃ a ∈ rootLine x i, ∃ b ∈ rootLine x j, dist a b = r} = 1 := by
  change lineDistance (toE3 (halfVec (pointsR x i))) (toE3 (directionsR x i))
    (toE3 (halfVec (pointsR x j))) (toE3 (directionsR x j)) = 1
  by_cases hlt : i < j
  · exact pair_geometry hroot hbox hlt
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    rw [lineDistance_comm]
    exact pair_geometry hroot hbox hji

theorem exists_seven_affine_lines :
    ∃ L : Fin 7 → AffineSubspace ℝ E3,
      (∀ i, Module.finrank ℝ (L i).direction = 1) ∧
      ∀ i j, i ≠ j →
        sInf {r : ℝ | ∃ a ∈ L i, ∃ b ∈ L j, dist a b = r} = 1 := by
  obtain ⟨x, hroot, hbox⟩ := exists_exact_distance_system_root
  exact ⟨rootLine x, rootLine_dimension x, fun i j hij =>
    rootLine_distance hroot hbox hij⟩

#print axioms pair_geometry
#print axioms exists_seven_affine_lines

end LittlewoodCylinders.LowerCertificate
