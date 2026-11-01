module
public import MathResearch.Analysis.RadialLaplacian
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Local radial Hessian formulas in real dimension four. These are used only
in the separate classical mean-value theorem. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped Quaternion ContDiff Topology
open InnerProductSpace Set Filter
namespace MathResearch.Spinor
local instance radialHessianLocalInstance0 : NormedAddCommGroup ℍ := inferInstance
local instance radialHessianLocalInstance1 : NormedSpace ℝ ℍ := inferInstance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance radialHessianLocalInstance2 : NormedAddCommGroup (ℍ →L[ℝ] E) := inferInstance
local instance radialHessianLocalInstance3 : NormedSpace ℝ (ℍ →L[ℝ] E) := inferInstance

theorem hasFDerivAt_quaternionNorm {q : ℍ} (hq : q ≠ 0) :
    HasFDerivAt (norm : ℍ → ℝ) (‖q‖⁻¹ • innerSL ℝ q) q := by
  have h := (hasStrictFDerivAt_norm_sq q).hasFDerivAt.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq))
  convert! h using 1
  · funext x
    simp
  · ext v
    simp only [Real.sqrt_sq (norm_nonneg q), smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    field_simp
    ring

/-- First radial derivative on the punctured ball. -/
theorem fderiv_radial_norm {A : ℍ → E} {M M' : ℝ → E}
    (hA : ∀ q ∈ Ball, A q = M ‖q‖)
    (hM : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt M (M' r) r)
    {q : ℍ} (hq : q ∈ Ball) (hq0 : q ≠ 0) (v : ℍ) :
    fderiv ℝ A q v = (‖q‖⁻¹ * inner ℝ q v) • M' ‖q‖ := by
  have hr : ‖q‖ ∈ Ioo (0:ℝ) 1 := ⟨norm_pos_iff.mpr hq0, (mem_ball_iff q).mp hq⟩
  have hd := (hM ‖q‖ hr).hasFDerivAt.comp q (hasFDerivAt_quaternionNorm hq0)
  have he : A =ᶠ[𝓝 q] (fun x => M ‖x‖) := by
    filter_upwards [ball_isOpen.mem_nhds hq] with x hx
    exact hA x hx
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- The radial Hessian in a tangential direction has eigenvalue M'(r)/r. -/
theorem radial_hessian_tangent {A : ℍ → E} {M M' M'' : ℝ → E}
    (hA : ∀ q ∈ Ball, A q = M ‖q‖)
    (hM : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt M (M' r) r)
    (hM' : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt M' (M'' r) r)
    {q : ℍ} (hq : q ∈ Ball) (hq0 : q ≠ 0)
    (hDA : DifferentiableAt ℝ (fderiv ℝ A) q)
    (v : ℍ) (hv : inner ℝ q v = 0) :
    fderiv ℝ (fderiv ℝ A) q v v = (‖v‖^2 / ‖q‖) • M' ‖q‖ := by
  have hr : ‖q‖ ∈ Ioo (0:ℝ) 1 := ⟨norm_pos_iff.mpr hq0, (mem_ball_iff q).mp hq⟩
  have hn := hasFDerivAt_quaternionNorm hq0
  have hi : HasFDerivAt (fun x : ℍ => inner ℝ x v) (innerSL ℝ v) q := by
    simpa only [coe_innerSL_apply, real_inner_comm] using (innerSL ℝ v).hasFDerivAt (x := q)
  have hc := ((hasDerivAt_inv (norm_ne_zero_iff.mpr hq0)).comp_hasFDerivAt q hn).mul hi
  have hd := hc.smul ((hM' ‖q‖ hr).hasFDerivAt.comp q hn)
  have he : (fun x => fderiv ℝ A x v) =ᶠ[𝓝 q]
      (fun x : ℍ => (‖x‖⁻¹ * inner ℝ x v) • M' ‖x‖) := by
    filter_upwards [ball_isOpen.mem_nhds hq, eventually_ne_nhds hq0] with x hx hx0
    exact fderiv_radial_norm hA hM hx hx0 v
  have H := (hd.congr_of_eventuallyEq he).fderiv
  have H' := congrArg (fun L : ℍ →L[ℝ] E => L v) H
  rw [fderiv_clm_apply hDA (differentiableAt_const _)] at H'
  simpa [hv, real_inner_self_eq_norm_sq, div_eq_mul_inv, mul_comm] using H'

end MathResearch.Spinor
