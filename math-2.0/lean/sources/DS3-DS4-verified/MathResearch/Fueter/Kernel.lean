module

public import MathResearch.Fueter.Operators
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! F1, formulation version 2: two-sided regularity of the quaternionic Cauchy
kernel and of every finite real coordinate derivative, away from zero. -/

@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff

namespace MathResearch.Fueter

/-- Supply the standard compatibility law from mathlib’s quaternion conjugation theorem. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by simpa only [star_trivial] using Quaternion.star_smul r q

/-- The domain in F1. No assertion of regularity at zero is made. -/
def punctured : Set ℍ := {0}ᶜ

theorem isOpen_punctured : IsOpen punctured := isClosed_singleton.isOpen_compl

/-- The F-D3 kernel. Real scalar division is written as scalar multiplication.
The total definition at zero is used only to supply an ambient function. -/
def kernel (q : ℍ) : ℍ := (Quaternion.normSq q)⁻¹ ^ 2 • star q

/-- Identification with the wiki's `conj(q) / |q|^4`. -/
theorem kernel_eq (q : ℍ) : kernel q = (‖q‖ ^ 4)⁻¹ • star q := by
  unfold kernel
  rw [Quaternion.normSq_eq_norm_mul_self, ← pow_two, ← inv_pow, ← pow_mul]
  rw [inv_pow]

/-- The norm-square polynomial is mathlib's quaternion norm square. -/
theorem contDiff_normSq : ContDiff ℝ ∞ (Quaternion.normSq : ℍ → ℝ) := by
  simpa only [pow_two, ← Quaternion.normSq_eq_norm_mul_self] using
    (contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun q : ℍ => ‖q‖ ^ 2)

theorem kernel_smooth : ContDiffOn ℝ ∞ kernel punctured := by
  have hi := contDiff_normSq.contDiffOn.inv (s := punctured)
    (fun q hq => Quaternion.normSq_ne_zero.mpr hq)
  exact (hi.pow 2).smul (starL' ℝ : ℍ ≃L[ℝ] ℍ).contDiff.contDiffOn

theorem fderiv_kernel {q : ℍ} (hq : q ≠ 0) (v : ℍ) :
    fderiv ℝ kernel q v =
      (Quaternion.normSq q)⁻¹ ^ 2 • star v -
        (4 * (Quaternion.normSq q)⁻¹ ^ 3 * inner ℝ q v) • star q := by
  have hn : HasFDerivAt (Quaternion.normSq : ℍ → ℝ) (2 • innerSL ℝ q) q := by
    simpa only [pow_two, ← Quaternion.normSq_eq_norm_mul_self] using
      (hasStrictFDerivAt_norm_sq q).hasFDerivAt
  have hi := (hasFDerivAt_inv (Quaternion.normSq_ne_zero.mpr hq)).comp q hn
  have hk := (hi.pow 2).smul ((hasFDerivAt_id q).star)
  change HasFDerivAt kernel _ q at hk
  rw [hk.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, inv_pow, Function.comp_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  module

/-- The left quaternion contraction, before substituting the radial coefficients. -/
theorem left_kernel_algebra (q : ℍ) (a b : ℝ) :
    (∑ μ : Fin 4, coordinateBasis μ *
      (a • star (coordinateBasis μ) - (b * inner ℝ q (coordinateBasis μ)) • star q)) =
        (4 * a - b * Quaternion.normSq q) • (1 : ℍ) := by
  ext <;> simp [Fin.sum_univ_succ, coordinateBasis_eq,
    Quaternion.inner_def, Quaternion.normSq_def'] <;> ring

/-- The corresponding right contraction keeps every quaternion factor in its order. -/
theorem right_kernel_algebra (q : ℍ) (a b : ℝ) :
    (∑ μ : Fin 4,
      (a • star (coordinateBasis μ) - (b * inner ℝ q (coordinateBasis μ)) • star q) *
        coordinateBasis μ) = (4 * a - b * Quaternion.normSq q) • (1 : ℍ) := by
  ext <;> simp [Fin.sum_univ_succ, coordinateBasis_eq,
    Quaternion.inner_def, Quaternion.normSq_def'] <;> ring

theorem kernel_left {q : ℍ} (hq : q ≠ 0) : leftOperator kernel q = 0 := by
  rw [leftOperator_eq]
  simp_rw [coordPartial, directional, fderiv_kernel hq]
  rw [left_kernel_algebra]
  have hs : Quaternion.normSq q ≠ 0 := Quaternion.normSq_ne_zero.mpr hq
  have hcoef : 4 * (Quaternion.normSq q)⁻¹ ^ 2 -
      4 * (Quaternion.normSq q)⁻¹ ^ 3 * Quaternion.normSq q = 0 := by
    field_simp
    ring
  rw [hcoef, zero_smul]

theorem kernel_right {q : ℍ} (hq : q ≠ 0) : rightOperator kernel q = 0 := by
  rw [rightOperator_eq]
  simp_rw [coordPartial, directional, fderiv_kernel hq]
  rw [right_kernel_algebra]
  have hs : Quaternion.normSq q ≠ 0 := Quaternion.normSq_ne_zero.mpr hq
  have hcoef : 4 * (Quaternion.normSq q)⁻¹ ^ 2 -
      4 * (Quaternion.normSq q)⁻¹ ^ 3 * Quaternion.normSq q = 0 := by
    field_simp
    ring
  rw [hcoef, zero_smul]

/-- F1 v2, first sentence: the kernel is smooth and both left and right regular off zero. -/
theorem kernel_regular : TwoSidedRegularOn kernel punctured :=
  ⟨kernel_smooth, fun _ hq => kernel_left hq, fun _ hq => kernel_right hq⟩

/-- A stronger ordered form: any finite string of real coordinate derivatives is regular. -/
theorem kernel_iteratedPartial_regular (l : List (Fin 4)) :
    TwoSidedRegularOn (iteratedPartial l kernel) punctured :=
  kernel_regular.iteratedPartial isOpen_punctured l

/-- F1, formulation version 2, including every real multi-index and both multiplication sides. -/
theorem F1_v2 : TwoSidedRegularOn kernel punctured ∧
    ∀ α : Fin 4 → ℕ, TwoSidedRegularOn (multiIndexPartial α kernel) punctured :=
  ⟨kernel_regular, fun α => kernel_regular.multiIndexPartial isOpen_punctured α⟩

end MathResearch.Fueter
