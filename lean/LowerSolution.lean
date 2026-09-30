import Mathlib
import LowerCertificateAlgebra

namespace LittlewoodCylinders.LowerCertificate

open scoped BigOperators Matrix
open LowerCertificateData

namespace Expr

@[simp] lemma eval_const' (q : ℚ) (z : V) : Expr.eval (.const q) z = q := rfl
@[simp] lemma eval_var' (i : I) (z : V) : Expr.eval (.var i) z = z i := rfl
@[simp] lemma eval_add' (a b : Expr) (z : V) : Expr.eval (a + b) z = a.eval z + b.eval z := rfl
@[simp] lemma eval_mul' (a b : Expr) (z : V) : Expr.eval (a * b) z = a.eval z * b.eval z := rfl
@[simp] lemma eval_neg' (a : Expr) (z : V) : Expr.eval (-a) z = -a.eval z := rfl
@[simp] lemma eval_sub' (a b : Expr) (z : V) : Expr.eval (a - b) z = a.eval z - b.eval z := rfl
@[simp] lemma eval_zero' (z : V) : Expr.eval (0 : Expr) z = 0 := by
  change Expr.eval (.const 0) z = 0
  norm_num [Expr.eval]
@[simp] lemma eval_one' (z : V) : Expr.eval (1 : Expr) z = 1 := by
  change Expr.eval (.const 1) z = 1
  norm_num [Expr.eval]
@[simp] lemma eval_two' (z : V) : Expr.eval (2 : Expr) z = 2 := by
  change Expr.eval (.const 2) z = 2
  rfl
@[simp] lemma eval_four' (z : V) : Expr.eval (4 : Expr) z = 4 := by
  change Expr.eval (.const 4) z = 4
  rfl

lemma eval_foldr_add (l : List Expr) (z : V) :
    Expr.eval (l.foldr (· + ·) 0) z = (l.map fun e => Expr.eval e z).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma eval_sum (f : I → Expr) (z : V) :
    Expr.eval (Expr.sum f) z = ∑ i : I, Expr.eval (f i) z := by
  rw [Expr.sum, eval_foldr_add, List.map_ofFn, List.sum_ofFn]
  rfl

end Expr

lemma radius_ne_zero_real : (radius : ℝ) ≠ 0 := by
  norm_num [radius]

lemma fixedPoint_implies_preconditioned_zero {z : V} (hz : fixedMap z = z) :
    preconditionerR *ᵥ (fun k => Expr.eval (shiftedEquations k) z) = 0 := by
  funext i
  have hi := congrFun hz i
  change Expr.eval (fixedPointMap i) z = z i at hi
  change z i - ((1 / radius : ℚ) : ℝ) *
    Expr.eval (Expr.sum fun k => .const (preconditioner i k) * shiftedEquations k) z = z i at hi
  rw [Expr.eval_sum] at hi
  simp only [Expr.eval] at hi
  push_cast at hi
  change (∑ k : I, (preconditioner i k : ℝ) *
    Expr.eval (shiftedEquations k) z) = 0
  have hm : (1 / (radius : ℝ)) *
      (∑ k : I, (preconditioner i k : ℝ) * Expr.eval (shiftedEquations k) z) = 0 := by
    linarith
  exact (mul_eq_zero.mp hm).resolve_left (one_div_ne_zero radius_ne_zero_real)

lemma fixedPoint_implies_equations {z : V} (hz : fixedMap z = z) :
    (fun k => Expr.eval (shiftedEquations k) z) = 0 := by
  apply preconditioner_mulVec_injective
  have hzero := fixedPoint_implies_preconditioned_zero hz
  change preconditionerR *ᵥ (fun k => Expr.eval (shiftedEquations k) z) =
    preconditionerR *ᵥ (0 : V)
  simpa using hzero

abbrev RVec3 := Fin 3 → ℝ

def vec3R (x y z : ℝ) : RVec3 := ![x, y, z]

def vsubR (a b : RVec3) : RVec3 := fun i => a i - b i

def crossR (a b : RVec3) : RVec3 :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def dotR (a b : RVec3) : ℝ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def pointsR (x : I → ℝ) : Fin 7 → RVec3 :=
  ![vec3R 0 0 (-1), vec3R 0 0 1,
    vec3R (x 0) (x 1) 0, vec3R (x 4) (x 5) 0,
    vec3R (x 8) (x 9) 0, vec3R (x 12) (x 13) 0,
    vec3R (x 16) (x 17) 0]

def directionsR (x : I → ℝ) : Fin 7 → RVec3 :=
  ![vec3R 1 0 0, vec3R 0 1 0,
    vec3R (x 2) (x 3) (1 - x 2 - x 3),
    vec3R (x 6) (x 7) (1 - x 6 - x 7),
    vec3R (x 10) (x 11) (1 - x 10 - x 11),
    vec3R (x 14) (x 15) (1 - x 14 - x 15),
    vec3R (x 18) (x 19) (1 - x 18 - x 19)]

def distanceSystemR (x : I → ℝ) : I → ℝ :=
  fun k =>
    let ij := pairIndex k
    let n := crossR (directionsR x ij.1) (directionsR x ij.2)
    let triple := dotR (vsubR (pointsR x ij.2) (pointsR x ij.1)) n
    triple * triple - 4 * dotR n n

attribute [reducible] vec3R vsubR crossR dotR pointsR directionsR distanceSystemR

lemma eval_vec3 (a b c : Expr) (z : V) :
    (fun q => Expr.eval (vec3 a b c q) z) =
      vec3R (Expr.eval a z) (Expr.eval b z) (Expr.eval c z) := by
  funext q
  fin_cases q <;> rfl

lemma eval_vsub (a b : Vec3) (z : V) :
    (fun q => Expr.eval (vsub a b q) z) =
      vsubR (fun q => Expr.eval (a q) z) (fun q => Expr.eval (b q) z) := by
  funext q
  change Expr.eval (a q) z - Expr.eval (b q) z =
    Expr.eval (a q) z - Expr.eval (b q) z
  rfl

lemma eval_cross (a b : Vec3) (z : V) :
    (fun q => Expr.eval (cross a b q) z) =
      crossR (fun q => Expr.eval (a q) z) (fun q => Expr.eval (b q) z) := by
  funext q
  fin_cases q <;> rfl

lemma eval_dot (a b : Vec3) (z : V) :
    Expr.eval (dot a b) z =
      dotR (fun q => Expr.eval (a q) z) (fun q => Expr.eval (b q) z) := by
  rfl

set_option maxHeartbeats 0 in
lemma eval_distanceSystem (x : I → Expr) (z : V) (k : I) :
    Expr.eval (distanceSystem x k) z =
      distanceSystemR (fun i => Expr.eval (x i) z) k := by
  fin_cases k <;>
    simp [distanceSystem, distanceSystemR, vec3, vec3R, vsub, vsubR,
      cross, crossR, dot, dotR, pointsR, directionsR, pairIndex]

abbrev actualVariables (z : V) : V := fun i => (center i : ℝ) + (radius : ℝ) * z i

lemma eval_shiftedVariables (z : V) :
    (fun i => Expr.eval (shiftedVariables i) z) = actualVariables z := by
  funext i
  simp [actualVariables, Expr.eval]

lemma eval_shiftedEquations (z : V) (k : I) :
    Expr.eval (shiftedEquations k) z = distanceSystemR (actualVariables z) k := by
  rw [shiftedEquations, eval_distanceSystem, eval_shiftedVariables]

lemma exists_exact_distance_system_root :
    ∃ x : V, (∀ k, distanceSystemR x k = 0) ∧
      ∀ i, |x i - (center i : ℝ)| ≤ (radius : ℝ) := by
  obtain ⟨z, hzbox, hzfix⟩ := exists_fixedPoint_in_unitCube
  refine ⟨actualVariables z, ?_, ?_⟩
  · intro k
    have hzero := congrFun (fixedPoint_implies_equations hzfix) k
    rw [eval_shiftedEquations] at hzero
    exact hzero
  · intro i
    have hzi := mem_unitCube_iff.mp hzbox i
    simp only [actualVariables]
    rw [show (center i : ℝ) + (radius : ℝ) * z i - (center i : ℝ) =
      (radius : ℝ) * z i by ring, abs_mul]
    have hr : |(radius : ℝ)| = (radius : ℝ) := abs_of_pos (by norm_num [radius])
    rw [hr]
    exact mul_le_of_le_one_right (by norm_num [radius]) hzi

#print axioms exists_exact_distance_system_root

end LittlewoodCylinders.LowerCertificate
