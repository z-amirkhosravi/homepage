module
public import MathResearch.Analysis.RadialLaplacian

/-! A regularized Newton potential in dimension four. The scalar cutoff is one
near zero and zero outside [-2,2]. No fundamental-solution theorem is assumed. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology
open MeasureTheory Filter Set Metric
namespace MathResearch.Spinor

/-- Fixed smooth cutoff of the squared radial variable. -/
def weylCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

theorem contDiff_weylCutoff : ContDiff ℝ ∞ (⇑weylCutoff : ℝ → ℝ) :=
  weylCutoff.contDiff

theorem contDiff_weylCutoff_deriv : ContDiff ℝ ∞ (deriv weylCutoff) :=
  contDiff_weylCutoff.deriv'

theorem contDiff_weylCutoff_deriv2 : ContDiff ℝ ∞ (deriv (deriv weylCutoff)) :=
  contDiff_weylCutoff_deriv.deriv'

/-- This vanishes near zero and equals -1/s outside the cutoff. -/
def weylProfile (s : ℝ) : ℝ := (weylCutoff s - 1) / s

theorem weylCutoff_one {s : ℝ} (hs : |s| ≤ 1) : weylCutoff s = 1 :=
  weylCutoff.one_of_mem_closedBall (by simpa [weylCutoff, Real.dist_eq] using hs)

theorem weylCutoff_zero {s : ℝ} (hs : 2 ≤ |s|) : weylCutoff s = 0 :=
  weylCutoff.zero_of_le_dist (by simpa [weylCutoff, Real.dist_eq] using hs)

theorem weylProfile_zero_near : weylProfile =ᶠ[𝓝 (0 : ℝ)] 0 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with s hs
  simp only [mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  simp [weylProfile, weylCutoff_one hs.le]

theorem contDiff_weylProfile : ContDiff ℝ ∞ weylProfile := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : s = 0
  · subst s
    exact contDiffAt_const.congr_of_eventuallyEq weylProfile_zero_near
  · exact (contDiff_weylCutoff.contDiffAt.sub contDiffAt_const).div contDiffAt_id hs

theorem deriv_weylProfile {s : ℝ} (hs : s ≠ 0) :
    deriv weylProfile s = (deriv weylCutoff s * s - weylCutoff s + 1) / s ^ 2 := by
  have hd := ((contDiff_weylCutoff.differentiable (by simp) s).hasDerivAt.sub_const 1).div
    (hasDerivAt_id s) hs
  change HasDerivAt weylProfile _ s at hd
  rw [hd.deriv]
  simp only [id_eq]
  ring

theorem deriv2_weylProfile {s : ℝ} (hs : s ≠ 0) :
    deriv (deriv weylProfile) s =
      (deriv (deriv weylCutoff) s * s ^ 2 - 2 * deriv weylCutoff s * s +
        2 * weylCutoff s - 2) / s ^ 3 := by
  have he : deriv weylProfile =ᶠ[𝓝 s]
      (fun t => (deriv weylCutoff t * t - weylCutoff t + 1) / t ^ 2) := by
    filter_upwards [eventually_ne_nhds hs] with t ht using deriv_weylProfile ht
  rw [he.deriv_eq]
  have hχ : Differentiable ℝ (⇑weylCutoff) := contDiff_weylCutoff.differentiable (by simp)
  have hχ' : Differentiable ℝ (deriv weylCutoff) :=
    contDiff_weylCutoff_deriv.differentiable (by simp)
  have hd := ((((hχ' s).hasDerivAt.mul (hasDerivAt_id s)).sub (hχ s).hasDerivAt).add_const 1).div
    ((hasDerivAt_id s).pow 2) (pow_ne_zero _ hs)
  dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_apply, id_eq] at hd
  change HasDerivAt (fun t => (deriv weylCutoff t * t - weylCutoff t + 1) / t ^ 2) _ s at hd
  rw [hd.deriv]
  field_simp
  ring

/-- The cancellation specific to dimension four. -/
theorem weylProfile_radial_identity (s : ℝ) :
    8 * deriv weylProfile s + 4 * s * deriv (deriv weylProfile) s =
      4 * deriv (deriv weylCutoff) s := by
  by_cases hs : s = 0
  · subst s
    have hχ : (⇑weylCutoff : ℝ → ℝ) =ᶠ[𝓝 0] (fun _ => 1) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      exact weylCutoff_one (le_of_lt (by simpa [mem_ball, Real.dist_eq] using ht))
    have hχ' : deriv weylCutoff =ᶠ[𝓝 0] (fun _ => 0) := by simpa using hχ.deriv
    rw [weylProfile_zero_near.deriv_eq, hχ'.deriv_eq]
    simp
  · rw [deriv_weylProfile hs, deriv2_weylProfile hs]
    field_simp
    ring

/-- Smooth regularized potential, equal to -|q|⁻² outside a ball. -/
def weylPotential (q : ℍ) : ℝ := weylProfile (‖q‖ ^ 2)

/-- Its Laplacian divided by four; a smooth compactly supported signed kernel. -/
def weylRawKernel (q : ℍ) : ℝ := deriv (deriv weylCutoff) (‖q‖ ^ 2)

theorem contDiff_weylPotential : ContDiff ℝ ∞ weylPotential :=
  contDiff_weylProfile.comp (contDiff_norm_sq ℝ)

theorem contDiff_weylRawKernel : ContDiff ℝ ∞ weylRawKernel :=
  contDiff_weylCutoff_deriv2.comp (contDiff_norm_sq ℝ)

theorem laplacian_weylPotential (q : ℍ) :
    Laplacian.laplacian weylPotential q = 4 * weylRawKernel q := by
  exact (laplacian_radial_sq weylProfile contDiff_weylProfile q).trans
    (weylProfile_radial_identity _)

theorem weylCutoff_zero_near {s : ℝ} (hs : 2 < |s|) :
    (⇑weylCutoff : ℝ → ℝ) =ᶠ[𝓝 s] 0 := by
  filter_upwards [(continuous_abs.tendsto s).eventually (Ioi_mem_nhds hs)] with t ht
  exact weylCutoff_zero ht.le

theorem weylCutoff_deriv_zero {s : ℝ} (hs : 2 < |s|) : deriv weylCutoff s = 0 := by
  rw [(weylCutoff_zero_near hs).deriv_eq]
  simp

theorem weylCutoff_deriv2_zero {s : ℝ} (hs : 2 < |s|) : deriv (deriv weylCutoff) s = 0 := by
  rw [(weylCutoff_zero_near hs).deriv.deriv_eq]
  simp

theorem weylRawKernel_zero {q : ℍ} (hq : 2 ≤ ‖q‖) : weylRawKernel q = 0 := by
  apply weylCutoff_deriv2_zero
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith

theorem weylRawKernel_tsupport : tsupport weylRawKernel ⊆ closedBall (0 : ℍ) 2 := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hn
  apply hq
  apply weylRawKernel_zero
  exact le_of_lt (by simpa only [mem_closedBall, dist_zero_right, not_le] using hn)

theorem hasCompactSupport_weylRawKernel : HasCompactSupport weylRawKernel :=
  (isCompact_closedBall (0 : ℍ) 2).of_isClosed_subset (isClosed_tsupport _) weylRawKernel_tsupport

/-- Exact radial mass, obtained from the antiderivative
`(r² χ'(r²) - χ(r²))/2`, not from an assumed fundamental-solution identity. -/
theorem weylRawKernel_radial_integral :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * deriv (deriv weylCutoff) (r ^ 2) = 1 / 2 := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) 2 ⊆ Ioi 0 from fun _ h => h.1)]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    have hd (r : ℝ) : HasDerivAt
        (fun t : ℝ => (t ^ 2 * deriv weylCutoff (t ^ 2) - weylCutoff (t ^ 2)) / 2)
        (r ^ 3 * deriv (deriv weylCutoff) (r ^ 2)) r := by
      have hχ := (contDiff_weylCutoff.differentiable (by simp) (r ^ 2)).hasDerivAt.comp r
        ((hasDerivAt_id r).pow 2)
      have hχ' := (contDiff_weylCutoff_deriv.differentiable (by simp) (r ^ 2)).hasDerivAt.comp r
        ((hasDerivAt_id r).pow 2)
      convert ((((hasDerivAt_id r).pow 2).mul hχ').sub hχ).div_const 2 using 1 <;>
        simp only [Function.comp_def, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
      ring
    have hi : IntervalIntegrable (fun r : ℝ => r ^ 3 * deriv (deriv weylCutoff) (r ^ 2))
        volume 0 2 :=
      (continuous_pow 3 |>.mul (contDiff_weylCutoff_deriv2.continuous.comp (continuous_pow 2))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi]
    norm_num [weylCutoff_deriv_zero (by norm_num : (2 : ℝ) < |4|),
      weylCutoff_zero (by norm_num : (2 : ℝ) ≤ |4|), weylCutoff_one (by norm_num : |(0 : ℝ)| ≤ 1)]
  · intro r hr
    have hr' : 2 < r := by simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hr; exact hr.2 hr.1
    rw [weylCutoff_deriv2_zero (by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith)]
    simp

/-- Nonzero mass of the signed smoothing kernel. -/
theorem integral_weylRawKernel : ∫ q, weylRawKernel q = 2 * volume.real (ball (0 : ℍ) 1) := by
  change (∫ q : ℍ, deriv (deriv weylCutoff) (‖q‖ ^ 2)) = _
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => deriv (deriv weylCutoff) (r ^ 2))]
  simp only [Quaternion.finrank_eq_four, Nat.reduceSub, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  rw [weylRawKernel_radial_integral]
  ring

end MathResearch.Spinor
