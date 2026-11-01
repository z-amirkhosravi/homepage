module
public import MathResearch.Spinor.WeakConstants

/-! Measure-theoretic consequences of DS2's actual Jacobian calculation. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal
open MeasureTheory
namespace MathResearch.Spinor

theorem measurable_mobiusDenominator (g : QuaternionMatrix2) : Measurable (mobiusDenominator g) := by
  unfold mobiusDenominator
  fun_prop

theorem measurable_mobiusPoint (g : QuaternionMatrix2) : Measurable (mobiusPoint g) := by
  unfold mobiusPoint
  exact (measurable_const.mul measurable_id |>.add measurable_const).mul
    (measurable_mobiusDenominator g).inv

def mobiusJacobianDensity (g : QuaternionMatrix2) (q : ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4)

theorem measurable_mobiusJacobianDensity (g : QuaternionMatrix2) :
    Measurable (mobiusJacobianDensity g) := by
  unfold mobiusJacobianDensity
  exact ((Quaternion.continuous_normSq.measurable.comp
    (measurable_mobiusDenominator g)).inv.pow_const _).ennreal_ofReal

theorem mobiusJacobianDensity_ne_zero {g : QuaternionMatrix2} (hg : IsSp11 g)
    {q : ℍ} (hq : q ∈ Ball) : mobiusJacobianDensity g q ≠ 0 := by
  apply ENNReal.ofReal_ne_zero_iff.mpr
  rw [Quaternion.normSq_eq_norm_mul_self]
  exact pow_pos (inv_pos.mpr (mul_pos (norm_pos_iff.mpr (mobiusDenominator_ne_zero hg hq))
    (norm_pos_iff.mpr (mobiusDenominator_ne_zero hg hq)))) _

/-- The written Jacobian formula as an equality of measures, not only total integrals. -/
theorem mobius_map_jacobian {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Measure.map (mobiusPoint g) ((volume.restrict Ball).withDensity (mobiusJacobianDensity g)) =
      volume.restrict Ball := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℍ)
    ball_isOpen.measurableSet.nullMeasurableSet
    (fun q hq => (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).hasFDerivWithinAt)
    (mobiusPoint_bijOn hg).injOn
  rw [(mobiusPoint_bijOn hg).image_eq] at h
  convert! h using 2
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  have hd : (mobiusDerivative g q).det = (Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4 := by
    rw [← (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).fderiv]
    exact mobiusJacobian g hg q hq
  dsimp only [mobiusJacobianDensity]
  rw [hd, abs_of_nonneg (by positivity)]

theorem mobius_quasiMeasurePreserving_volume {g : QuaternionMatrix2} (hg : IsSp11 g) :
    QuasiMeasurePreserving (mobiusPoint g) (volume.restrict Ball) (volume.restrict Ball) := by
  have ha : volume.restrict Ball ≪
      (volume.restrict Ball).withDensity (mobiusJacobianDensity g) :=
    withDensity_absolutelyContinuous' (measurable_mobiusJacobianDensity g).aemeasurable
      ((ae_restrict_mem ball_isOpen.measurableSet).mono fun _ hq => mobiusJacobianDensity_ne_zero hg hq)
  refine ⟨measurable_mobiusPoint g, ?_⟩
  simpa only [mobius_map_jacobian hg] using ha.map (measurable_mobiusPoint g)

theorem mobius_quasiMeasurePreserving_weighted (n : ℕ) (hn : 2 ≤ n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) :
    QuasiMeasurePreserving (mobiusPoint g) (weightedBallMeasure n) (weightedBallMeasure n) := by
  apply (mobius_quasiMeasurePreserving_volume hg).mono_left
    (withDensity_absolutelyContinuous _ _) |>.mono_right
  apply withDensity_absolutelyContinuous'
    (continuous_ballDensity n).measurable.ennreal_ofReal.aemeasurable
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  exact ENNReal.ofReal_ne_zero_iff.mpr (ballDensity_pos n hn hq)

theorem ballAction_aestronglyMeasurable (n : ℕ) (hn : 2 ≤ n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) {f : ℍ → BinaryForm n}
    (hf : AEStronglyMeasurable f (weightedBallMeasure n)) :
    AEStronglyMeasurable (ballAction n g f) (weightedBallMeasure n) := by
  have hcomp := hf.comp_quasiMeasurePreserving (mobius_quasiMeasurePreserving_weighted n hn hg)
  have hJ := (measurable_mobiusDenominator g).inv.aestronglyMeasurable (μ := weightedBallMeasure n)
  have hp := (contDiff_quaternionPolynomialRepresentation n).continuous.comp_aestronglyMeasurable
    (hJ.prodMk hcomp)
  exact ((Quaternion.continuous_normSq.measurable.comp
    (measurable_mobiusDenominator g)).inv.aestronglyMeasurable).smul hp

end MathResearch.Spinor
