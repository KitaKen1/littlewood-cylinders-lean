import Mathlib
import LowerSolution

namespace LittlewoodCylinders.LowerCertificate

open LowerCertificateData

abbrev ShiftVec3 := Fin 3 → Expr

def shiftedDirections : Fin 7 → ShiftVec3 :=
  ![vec3 1 0 0, vec3 0 1 0,
    vec3 (shiftedVariables 2) (shiftedVariables 3)
      (1 - shiftedVariables 2 - shiftedVariables 3),
    vec3 (shiftedVariables 6) (shiftedVariables 7)
      (1 - shiftedVariables 6 - shiftedVariables 7),
    vec3 (shiftedVariables 10) (shiftedVariables 11)
      (1 - shiftedVariables 10 - shiftedVariables 11),
    vec3 (shiftedVariables 14) (shiftedVariables 15)
      (1 - shiftedVariables 14 - shiftedVariables 15),
    vec3 (shiftedVariables 18) (shiftedVariables 19)
      (1 - shiftedVariables 18 - shiftedVariables 19)]

def crossNormExpr (i j : Fin 7) : Expr :=
  let n := cross (shiftedDirections i) (shiftedDirections j)
  dot n n

attribute [reducible] shiftedDirections crossNormExpr

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem crossNorm_range_positive_certificate :
    ∀ i j : Fin 7, i < j →
      0 < (Expr.range (crossNormExpr i j)).center -
        (Expr.range (crossNormExpr i j)).radius := by
  decide +kernel

theorem pairIndex_complete :
    ∀ i j : Fin 7, i < j → (i, j) ≠ (0, 1) →
      ∃ k : I, pairIndex k = (i, j) := by
  decide +kernel

lemma eval_shiftedDirections (z : V) :
    (fun i q => Expr.eval (shiftedDirections i q) z) = directionsR (actualVariables z) := by
  funext i q
  fin_cases i <;> fin_cases q <;>
    simp [shiftedDirections, directionsR, vec3, vec3R, actualVariables,
      shiftedVariables]

lemma eval_crossNormExpr (z : V) (i j : Fin 7) :
    Expr.eval (crossNormExpr i j) z =
      dotR (crossR (directionsR (actualVariables z) i)
        (directionsR (actualVariables z) j))
        (crossR (directionsR (actualVariables z) i)
          (directionsR (actualVariables z) j)) := by
  rw [crossNormExpr, eval_dot, eval_cross]
  have hi := congrFun (eval_shiftedDirections z) i
  have hj := congrFun (eval_shiftedDirections z) j
  rw [hi, hj]

lemma direction_cross_norm_pos {z : V} (hz : z ∈ unitCube)
    {i j : Fin 7} (hij : i < j) :
    0 < dotR (crossR (directionsR (actualVariables z) i)
        (directionsR (actualVariables z) j))
      (crossR (directionsR (actualVariables z) i)
        (directionsR (actualVariables z) j)) := by
  have hmem := Expr.eval_mem_range (crossNormExpr i j) (mem_unitCube_iff.mp hz)
  have hcert := crossNorm_range_positive_certificate i j hij
  rw [Expr.Ball.Contains] at hmem
  rw [eval_crossNormExpr] at hmem
  have hlo : ((Expr.range (crossNormExpr i j)).center : ℝ) -
      ((Expr.range (crossNormExpr i j)).radius : ℝ) ≤
      dotR (crossR (directionsR (actualVariables z) i)
          (directionsR (actualVariables z) j))
        (crossR (directionsR (actualVariables z) i)
          (directionsR (actualVariables z) j)) := by
    have hneg := (abs_le.mp hmem).1
    linarith
  have hcertR : 0 < ((Expr.range (crossNormExpr i j)).center : ℝ) -
      ((Expr.range (crossNormExpr i j)).radius : ℝ) := by
    exact_mod_cast hcert
  exact hcertR.trans_le hlo

#print axioms crossNorm_range_positive_certificate
#print axioms direction_cross_norm_pos

end LittlewoodCylinders.LowerCertificate
