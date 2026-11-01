module
public import MathResearch.Analysis.WeylProfile

/-! Normalized scaled Weyl kernels and their compact potential differences. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology
open MeasureTheory InnerProductSpace Filter Set Metric
namespace MathResearch.Spinor

def weylMass : ℝ := 2 * volume.real (ball (0 : ℍ) 1)

theorem weylMass_pos : 0 < weylMass := by
  apply mul_pos (by norm_num)
  exact ENNReal.toReal_pos (measure_ball_pos volume (0 : ℍ) (by norm_num)).ne'
    measure_ball_lt_top.ne

def weylKernel (q : ℍ) : ℝ := weylRawKernel q / weylMass

theorem contDiff_weylKernel : ContDiff ℝ ∞ weylKernel :=
  contDiff_weylRawKernel.div_const _

theorem weylKernel_zero {q : ℍ} (hq : 2 ≤ ‖q‖) : weylKernel q = 0 := by
  simp [weylKernel, weylRawKernel_zero hq]

theorem weylKernel_tsupport : tsupport weylKernel ⊆ closedBall (0 : ℍ) 2 :=
  by
    apply closure_minimal _ isClosed_closedBall
    intro q hq
    by_contra hn
    exact hq (weylKernel_zero (le_of_lt (by simpa only [mem_closedBall, dist_zero_right, not_le] using hn)))

theorem hasCompactSupport_weylKernel : HasCompactSupport weylKernel :=
  (isCompact_closedBall (0 : ℍ) 2).of_isClosed_subset (isClosed_tsupport _) weylKernel_tsupport

theorem integral_weylKernel : ∫ q, weylKernel q = 1 := by
  change (∫ q, weylRawKernel q / weylMass) = _
  rw [integral_div, integral_weylRawKernel]
  exact div_self weylMass_pos.ne'

def weylScaledKernel (r : ℝ) (q : ℍ) : ℝ := r⁻¹ ^ 4 * weylKernel (r⁻¹ • q)

def weylScaledPotential (r : ℝ) (q : ℍ) : ℝ := r⁻¹ ^ 2 * weylPotential (r⁻¹ • q)

theorem contDiff_weylScaledKernel (r : ℝ) : ContDiff ℝ ∞ (weylScaledKernel r) :=
  contDiff_const.mul (contDiff_weylKernel.comp (contDiff_id.const_smul r⁻¹))

theorem contDiff_weylScaledPotential (r : ℝ) : ContDiff ℝ ∞ (weylScaledPotential r) :=
  contDiff_const.mul (contDiff_weylPotential.comp (contDiff_id.const_smul r⁻¹))

theorem weylScaledKernel_zero {r : ℝ} (hr : 0 < r) {q : ℍ} (hq : 2 * r ≤ ‖q‖) :
    weylScaledKernel r q = 0 := by
  have hh : 2 ≤ ‖r⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (le_div_iff₀ hr).mpr hq
  simp [weylScaledKernel, weylKernel_zero hh]

theorem weylScaledKernel_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (weylScaledKernel r) ⊆ closedBall (0 : ℍ) (2 * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hn
  exact hq (weylScaledKernel_zero hr
    (le_of_lt (by simpa only [mem_closedBall, dist_zero_right, not_le] using hn)))

theorem hasCompactSupport_weylScaledKernel {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (weylScaledKernel r) :=
  (isCompact_closedBall (0 : ℍ) (2 * r)).of_isClosed_subset (isClosed_tsupport _)
    (weylScaledKernel_tsupport hr)

theorem integral_weylScaledKernel {r : ℝ} (hr : 0 < r) : ∫ q, weylScaledKernel r q = 1 := by
  change (∫ q, r⁻¹ ^ 4 * weylKernel (r⁻¹ • q)) = _
  rw [integral_const_mul, volume.integral_comp_inv_smul]
  simp [Quaternion.finrank_eq_four, integral_weylKernel, abs_of_nonneg (pow_nonneg hr.le _),
    smul_eq_mul, hr.ne']

theorem laplacian_weylScaledPotential (r : ℝ) (q : ℍ) :
    Laplacian.laplacian (weylScaledPotential r) q =
      (4 * weylMass) * weylScaledKernel r q := by
  change Laplacian.laplacian (r⁻¹ ^ 2 • (fun x => weylPotential (r⁻¹ • x))) q = _
  have hc : ContDiff ℝ ∞ (fun x : ℍ => weylPotential (r⁻¹ • x)) :=
    contDiff_weylPotential.comp (contDiff_id.const_smul r⁻¹)
  rw [laplacian_smul _ (hc.contDiffAt.of_le (by simp)),
    laplacian_dilate contDiff_weylPotential, laplacian_weylPotential]
  simp only [smul_eq_mul, weylScaledKernel, weylKernel]
  field_simp [weylMass_pos.ne']

/-- All scales have the same Newton tail. -/
theorem weylScaledPotential_tail {r : ℝ} (hr : 0 < r) {q : ℍ} (hq : 2 * r ≤ ‖q‖) :
    weylScaledPotential r q = -(‖q‖ ^ 2)⁻¹ := by
  have hqpos : 0 < ‖q‖ := lt_of_lt_of_le (mul_pos (by norm_num) hr) hq
  have hh : 2 ≤ ‖r⁻¹ • q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (le_div_iff₀ hr).mpr hq
  have hχ : weylCutoff (‖r⁻¹ • q‖ ^ 2) = 0 :=
    weylCutoff_zero (by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith)
  change r⁻¹ ^ 2 * ((weylCutoff (‖r⁻¹ • q‖ ^ 2) - 1) / ‖r⁻¹ • q‖ ^ 2) = _
  rw [hχ]
  simp only [zero_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  field_simp

end MathResearch.Spinor
