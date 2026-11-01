module
public import MathResearch.Spinor.MobiusJacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The actual weighted ball measure and its Möbius change-of-variables identity. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Matrix.Norms.Elementwise ENNReal
open MeasureTheory
namespace MathResearch.Spinor

instance quaternionMeasurableSpace : MeasurableSpace ℍ := borel ℍ
instance quaternionBorelSpace : BorelSpace ℍ := ⟨rfl⟩
instance binaryFormMeasurableSpace (n : ℕ) : MeasurableSpace (BinaryForm n) := borel (BinaryForm n)
instance binaryFormBorelSpace (n : ℕ) : BorelSpace (BinaryForm n) := ⟨rfl⟩

def weightConstant (n : ℕ) : ℝ := (n:ℝ)*(n-1:ℝ)/Real.pi^2

def ballDensity (n : ℕ) (q : ℍ) : ℝ := weightConstant n * ballScale q ^ (n-2)

/-- The measure C_n (1-|q|²)^(n-2) dv restricted to the unit ball. -/
def weightedBallMeasure (n : ℕ) : Measure ℍ :=
  (volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q))

abbrev BallL2 (n : ℕ) := Lp (BinaryForm n) 2 (weightedBallMeasure n)

theorem weightConstant_pos (n : ℕ) (hn : 2 ≤ n) : 0 < weightConstant n := by
  unfold weightConstant
  have : (2:ℝ) ≤ n := by exact_mod_cast hn
  exact div_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_pos Real.pi_pos)

theorem ballDensity_pos (n : ℕ) (hn : 2 ≤ n) {q : ℍ} (hq : q ∈ Ball) : 0 < ballDensity n q :=
  mul_pos (weightConstant_pos n hn) (pow_pos hq _)

theorem continuous_ballDensity (n : ℕ) : Continuous (ballDensity n) :=
  continuous_const.mul (contDiff_ballScale.continuous.pow _)

theorem mobiusPoint_inverse {g : QuaternionMatrix2} (hg : IsSp11 g) {q : ℍ} (hq : q ∈ Ball) :
    mobiusPoint (signatureAdjoint g) (mobiusPoint g q)=q := by
  rw [← mobiusPoint_mul _ _ (mobiusDenominator_ne_zero hg hq),hg.1,mobiusPoint_one]

theorem mobiusPoint_bijOn {g : QuaternionMatrix2} (hg : IsSp11 g) : Set.BijOn (mobiusPoint g) Ball Ball := by
  refine ⟨fun _ hq => mobiusPoint_mem_ball hg hq, ?_, ?_⟩
  · intro q hq r hr he
    have h := congrArg (mobiusPoint (signatureAdjoint g)) he
    simpa [mobiusPoint_inverse hg hq,mobiusPoint_inverse hg hr] using h
  · intro q hq
    refine ⟨mobiusPoint (signatureAdjoint g) q,mobiusPoint_mem_ball (isSp11_signatureAdjoint hg) hq,?_⟩
    simpa only [signatureAdjoint_involutive] using mobiusPoint_inverse (isSp11_signatureAdjoint hg) hq

theorem weighted_density_cancellation (n : ℕ) (hn : 2 ≤ n) {g : QuaternionMatrix2}
    (hg : IsSp11 g) {q : ℍ} (hq : q ∈ Ball) :
    (Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4 * ballDensity n (mobiusPoint g q) =
      ballDensity n q * (‖mobiusDenominator g q‖⁻¹ ^ (n+2))^2 := by
  rw [ballDensity,ballDensity,ballScale_mobius hg hq,Quaternion.normSq_eq_norm_mul_self]
  rw [show n+2=(n-2)+4 by omega,pow_add]
  simp only [div_pow,mul_pow,mul_inv_rev]
  rw [div_eq_mul_inv,mul_inv_rev]
  simp only [inv_pow]
  ring

/-- The weighted square norm is preserved, for arbitrary functions whenever the integral is defined. -/
theorem weighted_integral_ballAction (n : ℕ) (hn : 2 ≤ n) (f : ℍ → BinaryForm n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) :
    (∫ q in Ball, ballDensity n q * ‖ballAction n g f q‖^2) =
      ∫ q in Ball, ballDensity n q * ‖f q‖^2 := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℍ) ball_isOpen.measurableSet
    (fun q hq => (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).hasFDerivWithinAt)
    (mobiusPoint_bijOn hg).injOn (fun q => ballDensity n q * ‖f q‖^2)
  rw [(mobiusPoint_bijOn hg).image_eq] at h
  rw [h]
  apply setIntegral_congr_fun ball_isOpen.measurableSet
  intro q hq
  dsimp only
  rw [ballAction_norm]
  have hd : (mobiusDerivative g q).det=(Quaternion.normSq (mobiusDenominator g q))⁻¹ ^ 4 := by
    rw [← (hasFDerivAt_mobiusPoint g (mobiusDenominator_ne_zero hg hq)).fderiv]
    exact mobiusJacobian g hg q hq
  rw [hd,abs_of_nonneg (by positivity),smul_eq_mul,← mul_assoc,weighted_density_cancellation n hn hg hq,mul_pow]
  ring

end MathResearch.Spinor
