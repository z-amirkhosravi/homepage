module
public import MathResearch.Spinor.BallConnection

/-! The analytic scalar-weight cancellation in SC3, for actual Fueter derivatives. -/
@[expose] public section
noncomputable section
open scoped Quaternion BigOperators
namespace MathResearch.Spinor

/-- Real power of the ball defining function; smooth on the open ball for every real β. -/
def ballWeight (β : ℝ) (q : ℍ) : ℝ := (ballScale q) ^ β

theorem ballWeight_pos (β : ℝ) {q : ℍ} (hq : q ∈ Ball) : 0 < ballWeight β q :=
  Real.rpow_pos_of_pos hq β

theorem hasFDerivAt_ballWeight (β : ℝ) {q : ℍ} (hq : q ∈ Ball) :
    HasFDerivAt (ballWeight β) ((β * (ballScale q) ^ (β-1)) • ((-2 : ℝ) • innerSL ℝ q)) q :=
  (hasFDerivAt_ballScale q).rpow_const (Or.inl (ne_of_gt hq))

theorem basis_inner_contraction (q : ℍ) :
    (∑ μ : Fin 4, (inner ℝ q (Fueter.coordinateBasis μ)) • Fueter.coordinateBasis μ) = q := by
  ext <;> simp [Fueter.coordinateBasis_eq, Fin.sum_univ_succ, Quaternion.inner_def]

/-- Product rule with the precise left multiplication order. -/
theorem leftOperator_weight (β : ℝ) (h : ℍ → ℍ) {q : ℍ} (hq : q ∈ Ball)
    (hh : DifferentiableAt ℝ h q) :
    Fueter.leftOperator (fun x => ballWeight β x • h x) q =
      ballWeight β q • Fueter.leftOperator h q -
        (2 * β * (ballScale q) ^ (β-1)) • (q * h q) := by
  have hd := (hasFDerivAt_ballWeight β hq).fun_smul hh.hasFDerivAt
  rw [Fueter.leftOperator_eq, Fueter.leftOperator_eq]
  simp only [Fueter.coordPartial, Fueter.directional, hd.fderiv,
    add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul, mul_add]
  simp only [mul_smul_comm, Finset.sum_add_distrib, ← Finset.smul_sum]
  have hr : (∑ μ : Fin 4, ((β * ballScale q ^ (β-1)) * (-2 * inner ℝ q (Fueter.coordinateBasis μ))) •
      (Fueter.coordinateBasis μ * h q)) =
      -(2 * β * ballScale q ^ (β-1)) • (q * h q) := by
    have he : (∑ μ : Fin 4, (inner ℝ q (Fueter.coordinateBasis μ)) •
        (Fueter.coordinateBasis μ * h q)) = q * h q := by
      simpa [Finset.sum_mul, smul_mul_assoc] using congrArg (fun a : ℍ => a * h q) (basis_inner_contraction q)
    calc
      _ = -(2 * β * ballScale q ^ (β-1)) •
          (∑ μ : Fin 4, (inner ℝ q (Fueter.coordinateBasis μ)) • (Fueter.coordinateBasis μ * h q)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro μ _
        simp only [smul_smul]
        congr 1
        ring
      _ = _ := by rw [he]

  rw [hr]
  simp [sub_eq_add_neg]

theorem scale_mul_rpow_sub_one {s : ℝ} (hs : 0 < s) (β : ℝ) :
    s * s ^ (β-1) = s ^ β := by
  calc
    _ = s ^ (1 : ℝ) * s ^ (β-1) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hs]; congr 1; ring

theorem scale_mul_rpow {s : ℝ} (hs : 0 < s) (β : ℝ) :
    s * s ^ β = s ^ (β+1) := by
  calc
    _ = s ^ (1 : ℝ) * s ^ β := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hs]; congr 1; ring

/-- SC3's scalar cancellation, valid for every differentiable quaternion-valued coefficient. -/
theorem weighted_fueter_cancellation (n : ℕ) (h : ℍ → ℍ) {q : ℍ} (hq : q ∈ Ball)
    (hh : DifferentiableAt ℝ h q) :
    ballScale q • Fueter.leftOperator (fun x => ballWeight (((n:ℝ)+2)/2) x • h x) q +
      ((n:ℝ)+2) • (q * (ballWeight (((n:ℝ)+2)/2) q • h q)) =
        ballWeight (((n:ℝ)+4)/2) q • Fueter.leftOperator h q := by
  rw [leftOperator_weight _ h hq hh]
  simp only [smul_sub, smul_smul, mul_smul_comm, ballWeight]
  rw [scale_mul_rpow hq]
  have hc : ballScale q * (2 * (((n:ℝ)+2)/2) * ballScale q ^ ((((n:ℝ)+2)/2)-1)) =
      ((n:ℝ)+2) * ballScale q ^ (((n:ℝ)+2)/2) := by
    calc
      _ = ((n:ℝ)+2) * (ballScale q * ballScale q ^ ((((n:ℝ)+2)/2)-1)) := by ring
      _ = _ := by rw [scale_mul_rpow_sub_one hq]
  rw [hc]
  have he : (((n:ℝ)+2)/2)+1 = ((n:ℝ)+4)/2 := by ring
  rw [he]
  abel

theorem weighted_fueter_kernel_iff (n : ℕ) (h : ℍ → ℍ) {q : ℍ} (hq : q ∈ Ball)
    (hh : DifferentiableAt ℝ h q) :
    (ballScale q • Fueter.leftOperator (fun x => ballWeight (((n:ℝ)+2)/2) x • h x) q +
      ((n:ℝ)+2) • (q * (ballWeight (((n:ℝ)+2)/2) q • h q)) = 0) ↔
        Fueter.leftOperator h q = 0 := by
  rw [weighted_fueter_cancellation n h hq hh]
  exact smul_eq_zero_iff_right (ne_of_gt (ballWeight_pos _ hq))

end MathResearch.Spinor
