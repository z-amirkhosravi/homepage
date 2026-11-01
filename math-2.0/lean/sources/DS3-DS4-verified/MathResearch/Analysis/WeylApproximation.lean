module
public import MathResearch.Analysis.WeylTests

/-! Almost-everywhere recovery by the signed Weyl kernels. The convergence
uses mathlib's Lebesgue differentiation theorem, not a regularity assumption. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Topology Convolution
open MeasureTheory MeasureTheory.Measure Filter Set Metric ContinuousLinearMap
namespace MathResearch.Spinor

def weylRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem weylRadius_pos (k : ℕ) : 0 < weylRadius k := by unfold weylRadius; positivity

theorem weylRadius_tendsto : Tendsto weylRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The bound needed by the Lebesgue-point approximate-identity theorem. -/
theorem weylScaledKernel_bound : ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ q : ℍ,
    |weylScaledKernel r q| ≤ C / volume.real (closedBall (0 : ℍ) (2 * r)) := by
  obtain ⟨M, hM⟩ := hasCompactSupport_weylKernel.exists_bound_of_continuous
    contDiff_weylKernel.continuous
  let V := volume.real (closedBall (0 : ℍ) 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_closedBall_pos volume (0 : ℍ) (by norm_num)).ne' measure_closedBall_lt_top.ne
  refine ⟨M * 2 ^ 4 * V, fun r hr q => ?_⟩
  have hb : |weylScaledKernel r q| ≤ r⁻¹ ^ 4 * M := by
    simp only [weylScaledKernel, abs_mul, abs_pow, abs_inv, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (hM (r⁻¹ • q)) (pow_nonneg (inv_nonneg.mpr hr.le) _)
  apply hb.trans_eq
  rw [addHaar_real_closedBall' volume _ (by positivity), Quaternion.finrank_eq_four]
  change r⁻¹ ^ 4 * M = M * 2 ^ 4 * V / ((2 * r) ^ 4 * V)
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Relates the displayed smoothing integral to mathlib's convolution. -/
theorem weylSmooth_eq_convolution (r : ℝ) (u : ℍ → E) :
    weylSmooth r u = weylScaledKernel r ⋆[lsmul ℝ ℝ, volume] u := by
  funext a
  rw [convolution_eq_swap]
  rfl

theorem contDiff_weylSmooth {u : ℍ → E} (hu : LocallyIntegrable u volume)
    {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (weylSmooth r u) := by
  rw [weylSmooth_eq_convolution]
  exact (hasCompactSupport_weylScaledKernel hr).contDiff_convolution_left (lsmul ℝ ℝ)
    (contDiff_weylScaledKernel r) hu

variable [CompleteSpace E]

theorem ae_tendsto_weylSmooth {u : ℍ → E} (hu : LocallyIntegrable u volume) :
    ∀ᵐ a ∂volume, Tendsto (fun k => weylSmooth (weylRadius k) u a) atTop (𝓝 (u a)) := by
  obtain ⟨C, hC⟩ := weylScaledKernel_bound
  have hr : Tendsto (fun k => 2 * weylRadius k) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using weylRadius_tendsto.const_mul 2,
      Eventually.of_forall (fun k => mul_pos (by norm_num) (weylRadius_pos k))⟩
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hu] with a ha
  have havg := (ha.comp (Besicovitch.tendsto_filterAt volume a)).comp hr
  apply tendsto_integral_smul_of_tendsto_average_norm_sub C havg
  · exact Eventually.of_forall (fun k => hu.integrableOn_isCompact (isCompact_closedBall _ _))
  · apply tendsto_const_nhds.congr
    intro k
    rw [← integral_neg_eq_self]
    simpa only [sub_neg_eq_add, integral_add_left_eq_self] using (integral_weylScaledKernel (weylRadius_pos k)).symm
  · exact Eventually.of_forall (fun k =>
      subset_trans subset_closure (tsupport_reflect_translate_subset
        (weylScaledKernel_tsupport (weylRadius_pos k)) a))
  · filter_upwards with k q
    rw [addHaar_real_closedBall_center]
    exact hC _ (weylRadius_pos k) _

end MathResearch.Spinor
