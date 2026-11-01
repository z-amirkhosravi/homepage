module
public import MathResearch.Analysis.WeylKernel

/-! Compact test potentials show that smoothing a weakly harmonic function
is locally independent of the smoothing radius. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology Distributions
open MeasureTheory InnerProductSpace Filter Set Metric
namespace MathResearch.Spinor

theorem tsupport_reflect_translate_subset {f : ℍ → ℝ} {R : ℝ}
    (hf : tsupport f ⊆ closedBall 0 R) (a : ℍ) :
    tsupport (fun y => f (a - y)) ⊆ closedBall a R := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  have hm := hf (subset_closure hy)
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm_sub', zero_sub, norm_neg] using hm

theorem closedBall_subset_Ball {a : ℍ} {R : ℝ} (h : ‖a‖ + R < 1) :
    closedBall a R ⊆ Ball := by
  intro q hq
  apply (mem_ball_iff q).mpr
  have hq' : ‖q - a‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm_sub] using hq
  calc
    ‖q‖ ≤ ‖a‖ + ‖q - a‖ := by simpa [norm_sub_rev] using norm_le_insert a q
    _ ≤ ‖a‖ + R := by gcongr
    _ < 1 := h

def weylKernelTest (r : ℝ) (a : ℍ) (hr : 0 < r) (ha : ‖a‖ + 2 * r < 1) : BallTest where
  toFun y := weylScaledKernel r (a - y)
  contDiff' := (contDiff_weylScaledKernel r).comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := (isCompact_closedBall a (2 * r)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_reflect_translate_subset (weylScaledKernel_tsupport hr) a)
  tsupport_subset' := (tsupport_reflect_translate_subset (weylScaledKernel_tsupport hr) a).trans
    (closedBall_subset_Ball ha)

def weylPotentialDifference (r s : ℝ) : ℍ → ℝ := weylScaledPotential r - weylScaledPotential s

theorem contDiff_weylPotentialDifference (r s : ℝ) : ContDiff ℝ ∞ (weylPotentialDifference r s) :=
  (contDiff_weylScaledPotential r).sub (contDiff_weylScaledPotential s)

theorem weylPotentialDifference_tsupport {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    tsupport (weylPotentialDifference r s) ⊆ closedBall 0 (2 * max r s) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hh
  have hn : 2 * max r s ≤ ‖q‖ := le_of_lt (by simpa [mem_closedBall, dist_zero_right] using hh)
  apply hq
  change weylScaledPotential r q - weylScaledPotential s q = 0
  rw [weylScaledPotential_tail hr ((mul_le_mul_of_nonneg_left (le_max_left r s) (by norm_num)).trans hn),
    weylScaledPotential_tail hs ((mul_le_mul_of_nonneg_left (le_max_right r s) (by norm_num)).trans hn), sub_self]

def weylPotentialTest (r s : ℝ) (a : ℍ) (hr : 0 < r) (hs : 0 < s)
    (ha : ‖a‖ + 2 * max r s < 1) : BallTest where
  toFun y := weylPotentialDifference r s (a - y)
  contDiff' := (contDiff_weylPotentialDifference r s).comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := (isCompact_closedBall a (2 * max r s)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_reflect_translate_subset (weylPotentialDifference_tsupport hr hs) a)
  tsupport_subset' := (tsupport_reflect_translate_subset (weylPotentialDifference_tsupport hr hs) a).trans
    (closedBall_subset_Ball ha)

theorem laplacian_weylPotentialDifference (r s : ℝ) (q : ℍ) :
    Laplacian.laplacian (weylPotentialDifference r s) q =
      (4 * weylMass) * (weylScaledKernel r q - weylScaledKernel s q) := by
  rw [weylPotentialDifference, ((contDiff_weylScaledPotential r).contDiffAt.of_le (by simp)).laplacian_sub
    ((contDiff_weylScaledPotential s).contDiffAt.of_le (by simp))]
  simp only [laplacian_weylScaledPotential]
  ring

theorem testLaplacian_weylPotentialTest (r s : ℝ) (a : ℍ) (hr : 0 < r) (hs : 0 < s)
    (ha : ‖a‖ + 2 * max r s < 1) (y : ℍ) :
    testLaplacian (weylPotentialTest r s a hr hs ha) y =
      (4 * weylMass) * (weylScaledKernel r (a - y) - weylScaledKernel s (a - y)) := by
  rw [testLaplacian_eq]
  change Laplacian.laplacian (fun y => weylPotentialDifference r s (a - y)) y = _
  rw [laplacian_reflect_translate (contDiff_weylPotentialDifference r s),
    laplacian_weylPotentialDifference]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual convolution of the normalized kernel with u. -/
def weylSmooth (r : ℝ) (u : ℍ → E) (a : ℍ) : E :=
  ∫ y, weylScaledKernel r (a - y) • u y

/-- The weak Laplace equation forces every sufficiently local smoothing scale
to give the same value. The test potential is explicitly constructed above. -/
theorem weylSmooth_eq_of_distributionLaplacian_zero {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {a : ℍ} (ha : ‖a‖ + 2 * max r s < 1) :
    weylSmooth r u a = weylSmooth s u a := by
  have har : ‖a‖ + 2 * r < 1 := lt_of_le_of_lt (by gcongr; exact le_max_left r s) ha
  have has : ‖a‖ + 2 * s < 1 := lt_of_le_of_lt (by gcongr; exact le_max_right r s) ha
  have hir : Integrable (fun y => weylScaledKernel r (a - y) • u y) :=
    (weylKernelTest r a hr har).integrable_smul hu
  have his : Integrable (fun y => weylScaledKernel s (a - y) • u y) :=
    (weylKernelTest s a hs has).integrable_smul hu
  have hz := congrArg (fun T : 𝓓'(ballOpen, E) => T (weylPotentialTest r s a hr hs ha)) hΔ
  rw [distributionLaplacian_apply, Distribution.ofFun_apply hu] at hz
  simp only [testLaplacian_weylPotentialTest, mul_smul, sub_smul] at hz
  simp only [integral_smul, integral_sub hir his, zero_apply] at hz
  change (4 : ℝ) • weylMass • (weylSmooth r u a - weylSmooth s u a) = 0 at hz
  rw [← mul_smul] at hz
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) weylMass_pos.ne'))

end MathResearch.Spinor
