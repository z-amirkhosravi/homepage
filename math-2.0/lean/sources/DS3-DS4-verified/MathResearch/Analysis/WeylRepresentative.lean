module
public import MathResearch.Analysis.WeylApproximation

/-! Construction of a smooth representative of a distributionally harmonic
locally integrable function on the quaternionic unit ball. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology Distributions
open MeasureTheory Filter Set Metric
namespace MathResearch.Spinor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Choose one allowable scale at each interior point; local scale independence
will prove smoothness, despite the nonsmooth norm used to choose this scale. -/
def weylRepresentative (u : ℍ → E) (a : ℍ) : E :=
  weylSmooth ((1 - ‖a‖) / 4) u a

theorem weylRepresentative_eq_smooth {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    {r : ℝ} (hr : 0 < r) {a : ℍ} (ha : ‖a‖ + 2 * r < 1) :
    weylRepresentative u a = weylSmooth r u a := by
  have haB : ‖a‖ < 1 := by linarith
  apply weylSmooth_eq_of_distributionLaplacian_zero hu hΔ (by linarith) hr
  rcases le_total ((1 - ‖a‖) / 4) r with h | h
  · rw [max_eq_right h]; exact ha
  · rw [max_eq_left h]; linarith

theorem weylSmooth_cutoff_eq (u : ℍ → E) {r R : ℝ} (hr : 0 < r) {a : ℍ}
    (ha : ‖a‖ + 2 * r ≤ R) :
    weylSmooth r ((closedBall (0 : ℍ) R).indicator u) a = weylSmooth r u a := by
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ closedBall (0 : ℍ) R
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy]
    have hny : R < ‖y‖ := by simpa [mem_closedBall, dist_zero_right] using hy
    have ht := norm_le_insert a y
    have hz : 2 * r ≤ ‖a - y‖ := by linarith
    rw [weylScaledKernel_zero hr hz]
    simp

omit [NormedSpace ℝ E] in
theorem integrable_ball_cutoff {u : ℍ → E} (hu : LocallyIntegrableOn u Ball volume)
    {R : ℝ} (hR : R < 1) : Integrable ((closedBall (0 : ℍ) R).indicator u) := by
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact hu.integrableOn_compact_subset
    (closedBall_subset_Ball (a := 0) (by simpa using hR)) (isCompact_closedBall _ _)

/-- Every fixed smaller ball has a single globally smooth convolution expression. -/
theorem weylRepresentative_eq_on_ball {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    {S R : ℝ} (hSR : S < R) (hR : R < 1) :
    Set.EqOn (weylRepresentative u)
      (weylSmooth ((R - S) / 4) ((closedBall (0 : ℍ) R).indicator u)) (ball 0 S) := by
  intro a ha
  have hna : ‖a‖ < S := by simpa [mem_ball, dist_zero_right] using ha
  have hr : 0 < (R - S) / 4 := by linarith
  rw [weylSmooth_cutoff_eq u hr (by linarith)]
  exact weylRepresentative_eq_smooth hu hΔ hr (by linarith)

/-- Smoothness is established by equality to one fixed-radius convolution
on each smaller ball. -/
theorem contDiffOn_weylRepresentative {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) :
    ContDiffOn ℝ ∞ (weylRepresentative u) Ball := by
  intro a ha
  obtain ⟨S, haS, hS⟩ := exists_between ((mem_ball_iff a).mp ha)
  obtain ⟨R, hSR, hR⟩ := exists_between hS
  have hg := contDiff_weylSmooth (integrable_ball_cutoff hu hR).locallyIntegrable
    (show 0 < (R - S) / 4 by linarith)
  apply (hg.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_ball.mem_nhds (show a ∈ ball (0 : ℍ) S by simpa [mem_ball] using haS)] with x hx
  exact weylRepresentative_eq_on_ball hu hΔ hSR hR hx

variable [CompleteSpace E]

/-- The smooth representative agrees almost everywhere with u on each smaller ball. -/
theorem ae_weylRepresentative_on_ball {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    {S R : ℝ} (hSR : S < R) (hR : R < 1) :
    u =ᵐ[volume.restrict (ball (0 : ℍ) S)] weylRepresentative u := by
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [ae_tendsto_weylSmooth (integrable_ball_cutoff hu hR).locallyIntegrable] with a ha
  intro haS
  have hna : ‖a‖ < S := by simpa [mem_ball] using haS
  have ht : Tendsto (fun k => weylSmooth (weylRadius k) ((closedBall (0 : ℍ) R).indicator u) a)
      atTop (𝓝 (weylRepresentative u a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp weylRadius_tendsto).2 ((R - S) / 2) (by linarith)] with k hk
    rw [weylSmooth_cutoff_eq u (weylRadius_pos k) (by linarith)]
    exact weylRepresentative_eq_smooth hu hΔ (weylRadius_pos k) (by linarith)
  have he := tendsto_nhds_unique ha ht
  rwa [indicator_of_mem (show a ∈ closedBall (0 : ℍ) R by simp only [mem_closedBall, dist_zero_right]; linarith)] at he

/-- Countably many rational radii pass the local almost-everywhere equality to B. -/
theorem ae_weylRepresentative {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) :
    u =ᵐ[volume.restrict Ball] weylRepresentative u := by
  have hcover : Ball = ⋃ S : {s : ℚ // (s : ℝ) < 1}, ball (0 : ℍ) (S.val : ℝ) := by
    ext a
    constructor
    · intro ha
      obtain ⟨r, har, hr⟩ := exists_rat_btwn ((mem_ball_iff a).mp ha)
      exact mem_iUnion.mpr ⟨⟨r, hr⟩, by simpa [mem_ball] using har⟩
    · intro ha
      obtain ⟨r, hr⟩ := mem_iUnion.mp ha
      apply (mem_ball_iff a).mpr
      exact (show ‖a‖ < (r.val : ℝ) by simpa [mem_ball] using hr).trans r.property
  rw [hcover]
  apply (ae_restrict_iUnion_iff _ _).mpr
  intro S
  obtain ⟨R, hSR, hR⟩ := exists_between S.property
  exact ae_weylRepresentative_on_ball hu hΔ hSR hR

end MathResearch.Spinor
