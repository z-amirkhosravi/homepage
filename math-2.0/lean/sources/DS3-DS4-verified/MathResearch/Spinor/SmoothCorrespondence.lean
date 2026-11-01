module
public import MathResearch.Spinor.BallAction

/-! Smoothness of the explicit mutually inverse section/lift formulas. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise ContDiff
namespace MathResearch.Spinor

theorem contDiff_normSq : ContDiff ℝ ∞ (Quaternion.normSq : ℍ → ℝ) := by
  simpa only [id_eq, Quaternion.inner_self] using!
    (contDiff_id.inner ℝ contDiff_id : ContDiff ℝ ∞ (fun q : ℍ => inner ℝ q q))

theorem contDiff_ballScale : ContDiff ℝ ∞ ballScale :=
  contDiff_const.sub contDiff_normSq

theorem contDiffAt_ballWeight (β : ℝ) {q : ℍ} (hq : q ∈ Ball) : ContDiffAt ℝ ∞ (ballWeight β) q :=
  contDiff_ballScale.contDiffAt.rpow_const_of_ne (ne_of_gt hq)

theorem contDiffAt_ballSection {q : ℍ} (hq : q ∈ Ball) : ContDiffAt ℝ ∞ ballSection q := by
  have hr := (contDiff_ballScale.contDiffAt.sqrt (ne_of_gt hq)).inv (Real.sqrt_pos.mpr hq).ne'
  have hb : ContDiffAt ℝ ∞ (fun x : ℍ => (1 : QuaternionMatrix2) + tangentCLM x) q :=
    contDiffAt_const.add tangentCLM.contDiff.contDiffAt
  convert! hr.smul hb using 1
  funext x
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ballSection, tangentMatrix]

theorem contDiffAt_quaternionInv {q : ℍ} (hq : q ≠ 0) : ContDiffAt ℝ ∞ (Inv.inv : ℍ → ℍ) q := by
  simpa only [Ring.inverse_eq_inv'] using! contDiffAt_ringInverse ℝ (Units.mk0 q hq)

theorem contDiffAt_groupOrigin {g : QuaternionMatrix2} (hd : g 1 1 ≠ 0) : ContDiffAt ℝ ∞ groupOrigin g := by
  have he : ContDiffAt ℝ ∞ (entryCLM 1 1) g := (entryCLM 1 1).contDiff.contDiffAt
  simpa only [groupOrigin, entryCLM_apply] using!
    (entryCLM 0 1).contDiff.contDiffAt.mul ((contDiffAt_quaternionInv hd).comp g he)

theorem contDiffAt_fullLift (n : ℕ) (f : ℍ → BinaryForm n) {g : QuaternionMatrix2}
    (hg : IsSp11 g) (hf : ContDiffAt ℝ ∞ f (groupOrigin g)) : ContDiffAt ℝ ∞ (fullLift n f) g := by
  have hd : ContDiffAt ℝ ∞ (entryCLM 1 1) g := (entryCLM 1 1).contDiff.contDiffAt
  have hs := (contDiff_normSq.contDiffAt.comp g hd).inv (Quaternion.normSq_ne_zero.mpr hg.lowerRight_ne_zero)
  have hi := (contDiffAt_quaternionInv hg.lowerRight_ne_zero).comp g hd
  have hp := hi.prodMk (hf.comp g (contDiffAt_groupOrigin hg.lowerRight_ne_zero))
  have hr : ContDiffAt ℝ ∞ (fun x : QuaternionMatrix2 => polynomialRepresentation n (quaternionMatrix ((x 1 1)⁻¹)) (f (groupOrigin x))) g := by
    simpa only [Function.comp_def, entryCLM_apply] using!
      ((contDiff_quaternionPolynomialRepresentation n).contDiffAt.comp g hp)
  exact hs.smul hr

theorem contDiffAt_unweighted_section (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    {q : ℍ} (hq : q ∈ Ball) (hF : ContDiffAt ℝ ∞ F (ballSection q)) :
    ContDiffAt ℝ ∞ (unweightedSpinor n (fun x => F (ballSection x))) q :=
  (contDiffAt_ballWeight _ hq).smul (hF.comp q (contDiffAt_ballSection hq))

/-- The smooth lift and inverse section map are mutually inverse on their domains. -/
theorem SC3_smooth_correspondence_v1 (n : ℕ) :
    (∀ f : ℍ → BinaryForm n, (∀ q ∈ Ball, ContDiffAt ℝ ∞ f q) →
      RightEquivariant n (fullLift n f) ∧
      (∀ g, IsSp11 g → ContDiffAt ℝ ∞ (fullLift n f) g) ∧
      (∀ q ∈ Ball, unweightedSpinor n (fun x => fullLift n f (ballSection x)) q = f q)) ∧
    (∀ F : QuaternionMatrix2 → BinaryForm n, RightEquivariant n F →
      (∀ g, IsSp11 g → ContDiffAt ℝ ∞ F g) →
      (∀ q ∈ Ball, ContDiffAt ℝ ∞ (unweightedSpinor n (fun x => F (ballSection x))) q) ∧
      (∀ g, IsSp11 g → fullLift n (unweightedSpinor n (fun x => F (ballSection x))) g = F g)) := by
  constructor
  · intro f hf
    refine ⟨fullLift_rightEquivariant n f, fun g hg => contDiffAt_fullLift n f hg (hf _ (groupOrigin_mem_ball hg)), ?_⟩
    intro q hq
    change ballWeight _ q • fullLift n f (ballSection q) = f q
    rw [fullLift_section n f q hq]
    exact unweight_weight n f hq
  · intro F hK hF
    exact ⟨fun q hq => contDiffAt_unweighted_section n F hq (hF _ (ballSection_isSp11 q hq)),
      fun _ hg => fullLift_recover n F hK hg⟩

end MathResearch.Spinor
