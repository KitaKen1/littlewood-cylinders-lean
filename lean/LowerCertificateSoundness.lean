import Mathlib
import LowerCertificate

namespace LittlewoodCylinders.LowerCertificate

open scoped BigOperators
open Metric Set Function
open LowerCertificateData

namespace Expr.Ball

def Contains (a : Ball) (x : ℝ) : Prop :=
  |x - (a.center : ℝ)| ≤ (a.radius : ℝ)

theorem radius_nonneg_range (e : Expr) : 0 ≤ (Expr.range e).radius := by
  induction e with
  | const q => simp
  | var i => simp
  | add a b ha hb =>
      change 0 ≤ (Expr.range a).radius + (Expr.range b).radius
      exact add_nonneg ha hb
  | neg a ha => simpa [Expr.range, neg] using ha
  | mul a b ha hb =>
      positivity

theorem radius_nonneg_slope (e : Expr) (i : I) : 0 ≤ (Expr.slope e i).radius := by
  induction e with
  | const q => simp
  | var j => simp
  | add a b ha hb =>
      change 0 ≤ (Expr.slope a i).radius + (Expr.slope b i).radius
      exact add_nonneg ha hb
  | neg a ha => simpa [Expr.slope, neg] using ha
  | mul a b ha hb =>
      have hra := radius_nonneg_range a
      have hrb := radius_nonneg_range b
      positivity

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  simp [Contains]

theorem contains_unit {x : ℝ} (hx : |x| ≤ 1) : unit.Contains x := by
  simpa [Contains, unit]

theorem Contains.neg {a : Ball} {x : ℝ} (hx : a.Contains x) : a.neg.Contains (-x) := by
  rw [Contains, Ball.neg]
  push_cast
  rw [show -x - -(a.center : ℝ) = -(x - (a.center : ℝ)) by ring, abs_neg]
  exact hx

theorem Contains.add {a b : Ball} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x + y) := by
  rw [Contains, Ball.add]
  push_cast
  have htri : |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| ≤
      |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
  rw [show x + y - ((a.center : ℝ) + (b.center : ℝ)) =
      (x - (a.center : ℝ)) + (y - (b.center : ℝ)) by ring]
  exact htri.trans (add_le_add hx hy)

theorem Contains.mul {a b : Ball} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y)
    (hra : 0 ≤ a.radius) (hrb : 0 ≤ b.radius) : (a.mul b).Contains (x * y) := by
  rw [Contains, Ball.mul]
  push_cast
  have hxa : |x - (a.center : ℝ)| ≤ (a.radius : ℝ) := hx
  have hyb : |y - (b.center : ℝ)| ≤ (b.radius : ℝ) := hy
  have h1 := abs_mul (x - (a.center : ℝ)) (y - (b.center : ℝ))
  have h2 := abs_mul (a.center : ℝ) (y - (b.center : ℝ))
  have h3 := abs_mul (b.center : ℝ) (x - (a.center : ℝ))
  rw [show x * y - (a.center : ℝ) * (b.center : ℝ) =
      (x - (a.center : ℝ)) * (y - (b.center : ℝ)) +
      (a.center : ℝ) * (y - (b.center : ℝ)) +
      (b.center : ℝ) * (x - (a.center : ℝ)) by ring]
  calc
    |(x - (a.center : ℝ)) * (y - (b.center : ℝ)) +
        (a.center : ℝ) * (y - (b.center : ℝ)) +
        (b.center : ℝ) * (x - (a.center : ℝ))| ≤
        |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| +
        |(a.center : ℝ) * (y - (b.center : ℝ))| +
        |(b.center : ℝ) * (x - (a.center : ℝ))| := by
          exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ = |x - (a.center : ℝ)| * |y - (b.center : ℝ)| +
        |(a.center : ℝ)| * |y - (b.center : ℝ)| +
        |(b.center : ℝ)| * |x - (a.center : ℝ)| := by rw [h1, h2, h3]
    _ ≤ (a.radius : ℝ) * (b.radius : ℝ) +
        |(a.center : ℝ)| * (b.radius : ℝ) +
        |(b.center : ℝ)| * (a.radius : ℝ) := by
          have hra' : 0 ≤ (a.radius : ℝ) := by exact_mod_cast hra
          have hrb' : 0 ≤ (b.radius : ℝ) := by exact_mod_cast hrb
          have hp := mul_le_mul hxa hyb (abs_nonneg _) hra'
          have hca := mul_le_mul_of_nonneg_left hyb (abs_nonneg (a.center : ℝ))
          have hcb := mul_le_mul_of_nonneg_left hxa (abs_nonneg (b.center : ℝ))
          exact add_le_add (add_le_add hp hca) hcb
    _ = |(a.center : ℝ)| * (b.radius : ℝ) +
        |(b.center : ℝ)| * (a.radius : ℝ) +
        (a.radius : ℝ) * (b.radius : ℝ) := by ring

theorem Contains.abs_le_size {a : Ball} {x : ℝ} (hx : a.Contains x) :
    |x| ≤ (a.size : ℝ) := by
  rw [size]
  push_cast
  calc
    |x| = |(x - (a.center : ℝ)) + (a.center : ℝ)| := by ring_nf
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ)| := add_le_add_left hx _
    _ = |(a.center : ℝ)| + (a.radius : ℝ) := add_comm _ _

end Expr.Ball

namespace Expr

theorem eval_cast (e : Expr) (x : I → ℚ) :
    e.eval (fun i => (x i : ℝ)) = (e.evalQ x : ℝ) := by
  induction e with
  | const q => simp [eval, evalQ]
  | var i => simp [eval, evalQ]
  | add a b ha hb => simp [eval, evalQ, ha, hb]
  | mul a b ha hb => simp [eval, evalQ, ha, hb]
  | neg a ha => simp [eval, evalQ, ha]

theorem eval_mem_range (e : Expr) {x : I → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    (Expr.range e).Contains (e.eval x) := by
  induction e with
  | const q => exact Ball.contains_point q
  | var i => exact Ball.contains_unit (hx i)
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb =>
      exact ha.mul hb (Ball.radius_nonneg_range a) (Ball.radius_nonneg_range b)

def divided : Expr → I → (I → ℝ) → (I → ℝ) → ℝ
  | .const _, _, _, _ => 0
  | .var j, i, _, _ => if j = i then 1 else 0
  | .add a b, i, x, y => divided a i x y + divided b i x y
  | .mul a b, i, x, y => divided a i x y * b.eval x + a.eval y * divided b i x y
  | .neg a, i, x, y => -divided a i x y

theorem eval_sub_eq_coord_mul_divided (e : Expr) (i : I) (x y : I → ℝ)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    e.eval x - e.eval y = (x i - y i) * e.divided i x y := by
  induction e with
  | const q => simp [eval, divided]
  | var j =>
      by_cases hji : j = i
      · subst j; simp [eval, divided]
      · simp [eval, divided, hji, hxy j hji]
  | add a b ha hb =>
      simp only [eval, divided]
      calc
        a.eval x + b.eval x - (a.eval y + b.eval y) =
            (a.eval x - a.eval y) + (b.eval x - b.eval y) := by ring
        _ = (x i - y i) * a.divided i x y +
            (x i - y i) * b.divided i x y := by rw [ha, hb]
        _ = (x i - y i) * (a.divided i x y + b.divided i x y) := by ring
  | neg a ha =>
      simp only [eval, divided]
      calc
        -a.eval x - -a.eval y = -(a.eval x - a.eval y) := by ring
        _ = -((x i - y i) * a.divided i x y) := by rw [ha]
        _ = (x i - y i) * -a.divided i x y := by ring
  | mul a b ha hb =>
      simp only [eval, divided]
      rw [show a.eval x * b.eval x - a.eval y * b.eval y =
          (a.eval x - a.eval y) * b.eval x +
            a.eval y * (b.eval x - b.eval y) by ring, ha, hb]
      ring

theorem divided_mem_slope (e : Expr) (i : I) {x y : I → ℝ}
    (hx : ∀ j, |x j| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    (e.slope i).Contains (e.divided i x y) := by
  induction e with
  | const q => simpa [slope, divided] using Ball.contains_point 0
  | var j =>
      by_cases h : j = i
      · simp [divided, h, Ball.Contains]
      · simp [divided, h, Ball.Contains]
  | add a b ha hb => exact ha.add hb
  | neg a ha => exact ha.neg
  | mul a b ha hb =>
      exact (ha.mul (eval_mem_range b hx) (Ball.radius_nonneg_slope a i)
        (Ball.radius_nonneg_range b)).add
        ((eval_mem_range a hy).mul hb (Ball.radius_nonneg_range a)
          (Ball.radius_nonneg_slope b i))

def splice (x y : I → ℝ) (k : ℕ) : I → ℝ := fun i =>
  if i.val < k then x i else y i

theorem splice_zero (x y : I → ℝ) : splice x y 0 = y := by
  funext i
  simp [splice]

theorem splice_twenty (x y : I → ℝ) : splice x y 20 = x := by
  funext i
  simp [splice, i.isLt]

theorem splice_mem_unit {x y : I → ℝ} (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (k : ℕ) (i : I) : |splice x y k i| ≤ 1 := by
  simp only [splice]
  split_ifs <;> simp_all

theorem splice_succ_same_of_ne {x y : I → ℝ} {k : ℕ} (hk : k < 20) (j : I)
    (hji : j ≠ (⟨k, hk⟩ : I)) : splice x y (k + 1) j = splice x y k j := by
  simp only [splice]
  have hjk : j.val ≠ k := by
    intro h
    apply hji
    apply Fin.ext
    exact h
  by_cases hlt : j.val < k
  · simp [hlt, Nat.lt_succ_of_lt hlt]
  · have hgt : k < j.val := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hjk)
    simp [hlt, Nat.not_lt_of_ge hgt]

theorem splice_succ_sub (x y : I → ℝ) {k : ℕ} (hk : k < 20) :
    splice x y (k + 1) ⟨k, hk⟩ - splice x y k ⟨k, hk⟩ =
      x ⟨k, hk⟩ - y ⟨k, hk⟩ := by
  simp [splice]

theorem eval_step_le (e : Expr) {x y : I → ℝ}
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) {k : ℕ} (hk : k < 20) :
    |e.eval (splice x y (k + 1)) - e.eval (splice x y k)| ≤
      ((e.slope ⟨k, hk⟩).size : ℝ) * ‖x - y‖ := by
  let i : I := ⟨k, hk⟩
  have hfactor := e.eval_sub_eq_coord_mul_divided i (splice x y (k + 1)) (splice x y k)
    (fun j hji => splice_succ_same_of_ne hk j hji)
  rw [hfactor, abs_mul, splice_succ_sub x y hk]
  have hcoord : |x i - y i| ≤ ‖x - y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (x - y) i
  have hdiv := (e.divided_mem_slope i (splice_mem_unit hx hy (k + 1))
    (splice_mem_unit hx hy k)).abs_le_size
  have hsize : 0 ≤ ((e.slope i).size : ℝ) := by
    rw [Expr.Ball.size]
    push_cast
    exact add_nonneg (abs_nonneg _) (by exact_mod_cast Ball.radius_nonneg_slope e i)
  calc
    |x i - y i| * |e.divided i (splice x y (k + 1)) (splice x y k)| ≤
        ‖x - y‖ * ((e.slope i).size : ℝ) :=
      mul_le_mul hcoord hdiv (abs_nonneg _) (norm_nonneg _)
    _ = ((e.slope i).size : ℝ) * ‖x - y‖ := mul_comm _ _

def finIndex (k : ℕ) : I := ⟨k % 20, Nat.mod_lt _ (by decide)⟩

theorem eval_lipschitz_on_unit (e : Expr) {x y : I → ℝ}
    (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1) :
    |e.eval x - e.eval y| ≤
      ((∑ i : I, (e.slope i).size : ℚ) : ℝ) * ‖x - y‖ := by
  have htel := Finset.sum_range_sub (fun k => e.eval (splice x y k)) 20
  have hrewrite : e.eval x - e.eval y =
      ∑ k ∈ Finset.range 20,
        (e.eval (splice x y (k + 1)) - e.eval (splice x y k)) := by
    simpa [splice_zero, splice_twenty] using htel.symm
  rw [hrewrite]
  calc
    |∑ k ∈ Finset.range 20,
        (e.eval (splice x y (k + 1)) - e.eval (splice x y k))| ≤
        ∑ k ∈ Finset.range 20,
          |e.eval (splice x y (k + 1)) - e.eval (splice x y k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range 20,
        (((e.slope (finIndex k)).size : ℚ) : ℝ) *
          ‖x - y‖ := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hi : finIndex k = (⟨k, hk'⟩ : I) := by
        apply Fin.ext
        simp [finIndex, Nat.mod_eq_of_lt hk']
      rw [hi]
      exact eval_step_le e hx hy hk'
    _ = ((∑ i : I, (e.slope i).size : ℚ) : ℝ) * ‖x - y‖ := by
      push_cast
      simp [Finset.sum_range_succ, Fin.sum_univ_succ, finIndex]
      ring

end Expr

theorem contractionTotal_eq_certified :
    contractionTotal = certifiedContractionTotal := by
  rw [contractionTotal, certifiedContractionTotal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun (congrFun slope_certificate_matrix i) j]
  rfl

theorem residualTotal_eq_certified : residualTotal = certifiedResidualTotal := by
  rw [residualTotal, certifiedResidualTotal]
  apply Finset.sum_congr rfl
  intro i _
  rw [congrFun residual_certificate_vector i]

theorem contractionTotal_lt_half : contractionTotal < 1 / 2 := by
  rw [contractionTotal_eq_certified]
  exact certificate_contraction

theorem residual_add_contraction_lt_one : residualTotal + contractionTotal < 1 := by
  rw [residualTotal_eq_certified, contractionTotal_eq_certified]
  exact certificate_invariance

abbrev V := I → ℝ

def fixedMap (z : V) : V := fun i => Expr.eval (fixedPointMap i) z

def unitCube : Set V := Metric.closedBall 0 1

theorem mem_unitCube_iff {z : V} : z ∈ unitCube ↔ ∀ i, |z i| ≤ 1 := by
  rw [unitCube, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  simp [Real.norm_eq_abs]

theorem slope_size_nonneg (e : Expr) (i : I) : 0 ≤ (e.slope i).size := by
  rw [Expr.Ball.size]
  exact add_nonneg (abs_nonneg _) (Expr.Ball.radius_nonneg_slope e i)

theorem rowSlope_le_total (i : I) :
    ∑ j : I, (Expr.slope (fixedPointMap i) j).size ≤ contractionTotal := by
  rw [contractionTotal]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun k : I => ∑ j : I, (Expr.slope (fixedPointMap k) j).size)
    (fun k _ => Finset.sum_nonneg fun j _ => slope_size_nonneg (fixedPointMap k) j)
    (Finset.mem_univ i)

theorem fixedMap_lipschitz_on_unit {x y : V}
    (hx : x ∈ unitCube) (hy : y ∈ unitCube) :
    dist (fixedMap x) (fixedMap y) ≤ (1 / 2 : ℝ) * dist x y := by
  have hx' := mem_unitCube_iff.mp hx
  have hy' := mem_unitCube_iff.mp hy
  simp only [dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))]
  intro i
  simp only [fixedMap, Pi.sub_apply, Real.norm_eq_abs]
  have hi := Expr.eval_lipschitz_on_unit (fixedPointMap i) hx' hy'
  have hrowQ : (∑ j : I, (Expr.slope (fixedPointMap i) j).size) ≤ (1 / 2 : ℚ) :=
    rowSlope_le_total i |>.trans contractionTotal_lt_half.le
  have hrow :
      ((↑(∑ j : I, (Expr.slope (fixedPointMap i) j).size) : ℝ)) ≤ 1 / 2 := by
    calc
      (↑(∑ j : I, (Expr.slope (fixedPointMap i) j).size) : ℝ) ≤
          ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hrowQ
      _ = (1 / 2 : ℝ) := by norm_num
  calc
    |Expr.eval (fixedPointMap i) x - Expr.eval (fixedPointMap i) y| ≤
        ((↑(∑ j : I, (Expr.slope (fixedPointMap i) j).size) : ℝ)) * ‖x - y‖ := hi
    _ ≤ (1 / 2 : ℝ) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right hrow (norm_nonneg _)

theorem residual_coord_le_total (i : I) :
    |Expr.evalQ (fixedPointMap i) 0| ≤ residualTotal := by
  rw [residualTotal]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : I => |Expr.evalQ (fixedPointMap j) 0|)
    (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)

theorem fixedMap_mapsTo_unitCube : MapsTo fixedMap unitCube unitCube := by
  intro x hx
  rw [mem_unitCube_iff]
  intro i
  have hx' := mem_unitCube_iff.mp hx
  have hnorm : ‖x‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    simpa [Real.norm_eq_abs] using hx'
  have hz : ∀ j : I, |(0 : V) j| ≤ 1 := by intro j; norm_num
  have hlip := Expr.eval_lipschitz_on_unit (fixedPointMap i) hx' hz
  have hrow :
      ((↑(∑ j : I, (Expr.slope (fixedPointMap i) j).size) : ℝ)) ≤
        (contractionTotal : ℝ) := by
    exact_mod_cast rowSlope_le_total i
  have hres : |Expr.eval (fixedPointMap i) 0| ≤ (residualTotal : ℝ) := by
    have he : Expr.eval (fixedPointMap i) (0 : V) =
        (Expr.evalQ (fixedPointMap i) (0 : I → ℚ) : ℝ) :=
      by
        have hfun : (0 : V) = fun j => ((0 : I → ℚ) j : ℝ) := by
          funext j
          simp
        rw [hfun]
        exact Expr.eval_cast (fixedPointMap i) (0 : I → ℚ)
    rw [he]
    exact_mod_cast residual_coord_le_total i
  have htot : (residualTotal : ℝ) + (contractionTotal : ℝ) < 1 := by
    exact_mod_cast residual_add_contraction_lt_one
  calc
    |fixedMap x i| ≤
        |Expr.eval (fixedPointMap i) x - Expr.eval (fixedPointMap i) 0| +
          |Expr.eval (fixedPointMap i) 0| := by
      simp only [fixedMap]
      have := abs_add_le
        (Expr.eval (fixedPointMap i) x - Expr.eval (fixedPointMap i) 0)
        (Expr.eval (fixedPointMap i) 0)
      simpa using this
    _ ≤ ((↑(∑ j : I, (Expr.slope (fixedPointMap i) j).size) : ℝ)) *
          ‖x - 0‖ + (residualTotal : ℝ) := add_le_add hlip hres
    _ ≤ (contractionTotal : ℝ) + (residualTotal : ℝ) := by
      have hctQ : 0 ≤ contractionTotal := by
        rw [contractionTotal]
        exact Finset.sum_nonneg fun k _ =>
          Finset.sum_nonneg fun j _ => slope_size_nonneg (fixedPointMap k) j
      have hct : 0 ≤ (contractionTotal : ℝ) := Rat.cast_nonneg.mpr hctQ
      have hmul := mul_le_mul hrow hnorm (norm_nonneg _) hct
      simpa using add_le_add_right hmul (residualTotal : ℝ)
    _ ≤ 1 := by simpa [add_comm] using htot.le

theorem fixedMap_contracting :
    ContractingWith (1 / 2 : NNReal)
      (fixedMap_mapsTo_unitCube.restrict fixedMap unitCube unitCube) := by
  constructor
  · norm_num
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (fixedMap x) (fixedMap y) ≤ (1 / 2 : ℝ) * dist (↑x : V) ↑y
    exact fixedMap_lipschitz_on_unit x.property y.property

theorem exists_fixedPoint_in_unitCube :
    ∃ z ∈ unitCube, fixedMap z = z := by
  have hzero : (0 : V) ∈ unitCube := mem_unitCube_iff.mpr fun _ => by simp
  have hfinite : edist (0 : V) (fixedMap 0) ≠ ⊤ := edist_ne_top _ _
  rcases fixedMap_contracting.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
      fixedMap_mapsTo_unitCube hzero hfinite with ⟨z, hz, hfix, _⟩
  exact ⟨z, hz, hfix⟩

end LittlewoodCylinders.LowerCertificate
