module
public import MathResearch.Spinor.RegularOrbit
public import MathResearch.Analysis.HarmonicMeanValue
public import MathResearch.Analysis.QuotientHaarIntegration

/-! C12: the actual Hilbert matrix coefficient agrees with the lifted function.
The harmonic radial mean-value theorem is a named external hypothesis. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

/-- Coefficient in mathlib's linear-second convention, equivalent to the
written ⟨π(g⁻¹)f,c_v⟩ in the linear-first convention. -/
def regularCoefficient (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n)
    (f : WeakBallSpace n hn) (g : Sp11) : ℂ :=
  inner ℂ (constantRegularIsometry n hn v) (regularRepresentation n hn g⁻¹ f)

theorem regularCoefficient_continuous (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n)
    (f : WeakBallSpace n hn) : Continuous (regularCoefficient n hn v f) :=
  continuous_const.inner ((stronglyContinuous_regularRepresentation_by_compact n hn f).comp continuous_inv)

theorem regularCoefficient_intertwines (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n)
    (f : WeakBallSpace n hn) (a g : Sp11) :
    regularCoefficient n hn v (regularRepresentation n hn a f) g =
      regularCoefficient n hn v f (a⁻¹*g) := by
  unfold regularCoefficient
  congr 1
  simp only [mul_inv_rev, inv_inv, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem regular_inner_constant (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n) (f : WeakBallSpace n hn) :
    inner ℂ (constantRegularIsometry n hn v) f = inner ℂ v (regularOrigin n hn f) := by
  obtain ⟨F, hF, hH, _, he⟩ := regularKernel_smooth_harmonic_classical n hn f
  have hLp : MemLp F 2 (weightedBallMeasure n) := (Lp.memLp f.val).ae_eq he
  have hi : Integrable F (weightedBallMeasure n) := hLp.integrable (by norm_num)
  change inner ℂ (constantRegularIsometry n hn v).val f.val = _
  rw [L2.inner_def]
  calc
    _ = ∫ q, inner ℂ v (F q) ∂weightedBallMeasure n := by
      apply integral_congr_ae
      filter_upwards [he, (memLp_const (p := 2) (μ := weightedBallMeasure n) v).coeFn_toLp] with q hq hvq
      change inner ℂ (Lp.const 2 (weightedBallMeasure n) v q) (f.val q) = _
      rw [← MemLp.toLp_const, hvq, hq]
    _ = inner ℂ v (∫ q, F q ∂weightedBallMeasure n) := integral_inner hi v
    _ = inner ℂ v (F 0) := by rw [meanValue (BinaryForm n) n hn F hF hH hi]
    _ = _ := by rw [regularOrigin, regularEvaluation_eq_representative n hn 0 _ f hF.continuousOn he]

/-- The exact C12 identity, for every smooth representative of the Hilbert vector. -/
theorem regularCoefficient_eq_lift (meanValue : RadialMeanValueOnBall)
    (n : ℕ) (hn : 2 ≤ n) (v : BinaryForm n) (f : WeakBallSpace n hn)
    (F : ℍ → BinaryForm n) (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) (g : Sp11) :
    regularCoefficient n hn v f g = liftedCoefficient n v F g := by
  rw [regularCoefficient, regular_inner_constant meanValue, regularOrigin,
    regularEvaluation_action n hn g⁻¹ f F hF he]
  change inner ℂ v (ballAction n (signatureAdjoint (signatureAdjoint g)) F 0) = _
  rw [signatureAdjoint_involutive, ballAction_zero_eq_fullLift]
  rfl

end MathResearch.Spinor
