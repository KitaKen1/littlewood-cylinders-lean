import Mathlib
import LowerCertificateData

/-!
# A kernel-checked existence certificate for seven equidistant lines

The numerical center comes from Bozoki--Lee--Ronyai.  The proof does not trust
the decimal approximation: `certificate_contraction` and
`certificate_invariance` below are exact computations in `ℚ`.
-/

namespace LittlewoodCylinders.LowerCertificate

open scoped BigOperators Matrix
open LowerCertificateData

inductive Expr where
  | const : ℚ → Expr
  | var : I → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
deriving Repr

namespace Expr

instance instOfNat (n : Nat) : OfNat Expr n := ⟨.const n⟩
instance instNeg : Neg Expr := ⟨.neg⟩
instance instAdd : Add Expr := ⟨.add⟩
instance instSub : Sub Expr := ⟨fun a b => .add a (.neg b)⟩
instance instMul : Mul Expr := ⟨.mul⟩

def sum (f : I → Expr) : Expr := (List.ofFn f).foldr (· + ·) 0

def evalQ : Expr → (I → ℚ) → ℚ
  | .const q, _ => q
  | .var i, x => x i
  | .add a b, x => evalQ a x + evalQ b x
  | .mul a b, x => evalQ a x * evalQ b x
  | .neg a, x => -evalQ a x

def eval : Expr → (I → ℝ) → ℝ
  | .const q, _ => q
  | .var i, x => x i
  | .add a b, x => eval a x + eval b x
  | .mul a b, x => eval a x * eval b x
  | .neg a, x => -eval a x

def derivEvalQ : Expr → I → (I → ℚ) → ℚ
  | .const _, _, _ => 0
  | .var j, i, _ => if j = i then 1 else 0
  | .add a b, i, x => derivEvalQ a i x + derivEvalQ b i x
  | .mul a b, i, x =>
      derivEvalQ a i x * evalQ b x + evalQ a x * derivEvalQ b i x
  | .neg a, i, x => -derivEvalQ a i x

@[ext] structure Ball where
  center : ℚ
  radius : ℚ
deriving Repr, DecidableEq

namespace Ball

def point (q : ℚ) : Ball := ⟨q, 0⟩
def unit : Ball := ⟨0, 1⟩
def neg (a : Ball) : Ball := ⟨-a.center, a.radius⟩
def add (a b : Ball) : Ball := ⟨a.center + b.center, a.radius + b.radius⟩
def mul (a b : Ball) : Ball :=
  ⟨a.center * b.center,
    |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius⟩
def size (a : Ball) : ℚ := |a.center| + a.radius

end Ball

def range : Expr → Ball
  | .const q => .point q
  | .var _ => .unit
  | .add a b => (range a).add (range b)
  | .mul a b => (range a).mul (range b)
  | .neg a => (range a).neg

/-- Interval enclosure of the exact one-coordinate divided difference. -/
def slope : Expr → I → Ball
  | .const _, _ => .point 0
  | .var j, i => .point (if j = i then 1 else 0)
  | .add a b, i => (slope a i).add (slope b i)
  | .mul a b, i => ((slope a i).mul (range b)).add ((range a).mul (slope b i))
  | .neg a, i => (slope a i).neg

end Expr

abbrev Vec3 := Fin 3 → Expr

def vec3 (x y z : Expr) : Vec3 := ![x, y, z]

def vsub (a b : Vec3) : Vec3 := fun i => a i - b i

def cross (a b : Vec3) : Vec3 :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def dot (a b : Vec3) : Expr := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def pairIndex : Fin 20 → Fin 7 × Fin 7 :=
  ![(0, 2), (0, 3), (0, 4), (0, 5), (0, 6),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 4), (3, 5), (3, 6),
    (4, 5), (4, 6), (5, 6)]

def distanceSystem (x : I → Expr) : I → Expr :=
  let p : Fin 7 → Vec3 :=
    ![vec3 0 0 (-1), vec3 0 0 1,
      vec3 (x 0) (x 1) 0, vec3 (x 4) (x 5) 0,
      vec3 (x 8) (x 9) 0, vec3 (x 12) (x 13) 0,
      vec3 (x 16) (x 17) 0]
  let w : Fin 7 → Vec3 :=
    ![vec3 1 0 0, vec3 0 1 0,
      vec3 (x 2) (x 3) (1 - x 2 - x 3),
      vec3 (x 6) (x 7) (1 - x 6 - x 7),
      vec3 (x 10) (x 11) (1 - x 10 - x 11),
      vec3 (x 14) (x 15) (1 - x 14 - x 15),
      vec3 (x 18) (x 19) (1 - x 18 - x 19)]
  fun k =>
    let ij := pairIndex k
    let n := cross (w ij.1) (w ij.2)
    let triple := dot (vsub (p ij.2) (p ij.1)) n
    triple * triple - 4 * dot n n

def originalVariables : I → Expr := Expr.var
def equations : I → Expr := distanceSystem originalVariables

def shiftedVariables : I → Expr := fun i =>
  .const (center i) + .const radius * .var i

def shiftedEquations : I → Expr := distanceSystem shiftedVariables

def fixedPointMap : I → Expr := fun i =>
  .var i - .const (1 / radius) *
    Expr.sum fun k => .const (preconditioner i k) * shiftedEquations k

def contractionTotal : ℚ :=
  ∑ i : I, ∑ j : I, (Expr.slope (fixedPointMap i) j).size

def residualTotal : ℚ :=
  ∑ i : I, |Expr.evalQ (fixedPointMap i) 0|

def computedJacobian : Matrix I I ℚ := fun i j => Expr.derivEvalQ (equations i) j center

def inverseErrorTotal : ℚ :=
  ∑ i : I, ∑ j : I,
    |(if i = j then 1 else 0) - ∑ k : I, preconditioner i k * jacobian k j|

def certifiedContractionTotal : ℚ :=
  ∑ i : I, ∑ j : I, (|slopeCenters i j| + slopeRadii i j)

def certifiedResidualTotal : ℚ := ∑ i : I, |residuals i|

def certifiedInverseErrorTotal : ℚ :=
  ∑ i : I, ∑ j : I,
    |(if i = j then 1 else 0) - ∑ k : I, preconditioner i k *
      LowerCertificateData.jacobian k j|

attribute [reducible] Expr.sum Expr.evalQ Expr.derivEvalQ Expr.range Expr.slope
  Expr.Ball.point Expr.Ball.unit Expr.Ball.neg Expr.Ball.add Expr.Ball.mul
  vec3 vsub cross dot pairIndex distanceSystem shiftedVariables shiftedEquations
  fixedPointMap

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem slope_certificate_00 :
    Expr.slope (fixedPointMap 0) 0 = ⟨slopeCenters 0 0, slopeRadii 0 0⟩ := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem slope_certificate_matrix :
    (fun i j => Expr.slope (fixedPointMap i) j) =
      (fun i j => ⟨slopeCenters i j, slopeRadii i j⟩) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem residual_certificate_vector :
    (fun i => Expr.evalQ (fixedPointMap i) 0) = residuals := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate_contraction : certifiedContractionTotal < 1 / 2 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate_invariance :
    certifiedResidualTotal + certifiedContractionTotal < 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate_preconditioner : certifiedInverseErrorTotal < 1 / 2 := by
  decide +kernel

#print axioms slope_certificate_matrix
#print axioms residual_certificate_vector
#print axioms certificate_contraction
#print axioms certificate_invariance
#print axioms certificate_preconditioner

end LittlewoodCylinders.LowerCertificate
