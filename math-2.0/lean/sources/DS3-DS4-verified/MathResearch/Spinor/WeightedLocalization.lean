module
public import MathResearch.Spinor.WeakConstants
public import Mathlib.Analysis.Distribution.Distribution

/-! Local Lebesgue integrability and the ordinary distribution attached to a weighted L² spinor. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Distributions ENNReal
open MeasureTheory
namespace MathResearch.Spinor

/-- Weighted L² convergence/regularity can be studied using ordinary Lebesgue distributions. -/
theorem memLp_locallyIntegrableOn_ball (n : ℕ) (hn : 2 ≤ n) {f : ℍ → BinaryForm n}
    (hf : MemLp f 2 (weightedBallMeasure n)) : LocallyIntegrableOn f Ball volume := by
  have hi : Integrable f (weightedBallMeasure n) := hf.integrable (by norm_num)
  have hw : IntegrableOn (fun q => ballDensity n q • f q) Ball volume := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (continuous_ballDensity n).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
    apply h.congr
    filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
    rw [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]
  have hc : ContinuousOn (fun q => (ballDensity n q)⁻¹) Ball :=
    (continuous_ballDensity n).continuousOn.inv₀ (fun q hq => (ballDensity_pos n hn hq).ne')
  have hl := hw.locallyIntegrableOn.continuousOn_smul ball_isOpen.isLocallyClosed hc
  apply hl.congr
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  simp only [smul_smul, inv_mul_cancel₀ (ballDensity_pos n hn hq).ne', one_smul]

theorem ballL2_locallyIntegrableOn (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    LocallyIntegrableOn (fun q => f q) Ball volume := memLp_locallyIntegrableOn_ball n hn (Lp.memLp f)

/-- This uses mathlib's distribution space, tested against all real smooth compact tests. -/
def spinorDistribution (n : ℕ) (f : BallL2 n) : 𝓓'(ballOpen, BinaryForm n) :=
  Distribution.ofFun ballOpen (fun q => f q) volume ⊤

theorem spinorDistribution_apply (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) (φ : BallTest) :
    spinorDistribution n f φ = ∫ q in Ball, φ q • f q := by
  rw [spinorDistribution, Distribution.ofFun_apply (ballL2_locallyIntegrableOn n hn f)]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by
    simp [φ.zero_on_compl hq]).symm

/-- The distribution determines the weighted L² class. -/
theorem spinorDistribution_injective (n : ℕ) (hn : 2 ≤ n) : Function.Injective (spinorDistribution n) := by
  intro f g h
  apply Lp.ext
  exact (ae_weightedBall_iff n hn (fun q => f q = g q)).mpr
    (Distribution.ofFun_injective (ballL2_locallyIntegrableOn n hn f)
      (ballL2_locallyIntegrableOn n hn g) h)

end MathResearch.Spinor
