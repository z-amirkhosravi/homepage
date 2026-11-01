module
public import MathResearch.Spinor.CompactGroup

/-! Pointwise formulas for the concrete regular action and the transitivity
step of the internal irreducibility argument. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion ContDiff
open MeasureTheory
namespace MathResearch.Spinor

theorem regularEvaluation_ext (n : ℕ) (hn : 2 ≤ n) (f h : WeakBallSpace n hn)
    (he : ∀ q (hq : q ∈ Ball), regularEvaluation n hn q hq f = regularEvaluation n hn q hq h) :
    f = h := by
  obtain ⟨F, hF, _, hf⟩ := weakKernel_classicalRepresentative n hn f
  obtain ⟨H, hH, _, hh⟩ := weakKernel_classicalRepresentative n hn h
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hf, hh, ae_mem_ball n hn] with q hfq hhq hq
  rw [hfq, hhq]
  rw [← regularEvaluation_eq_representative n hn q hq f hF.continuousOn hf,
    ← regularEvaluation_eq_representative n hn q hq h hH.continuousOn hh]
  exact he q hq

theorem regularEvaluation_constant (n : ℕ) (hn : 2 ≤ n) (q : ℍ) (hq : q ∈ Ball)
    (v : BinaryForm n) : regularEvaluation n hn q hq (constantRegularIsometry n hn v) = v := by
  apply regularEvaluation_eq_representative n hn q hq _ continuousOn_const
  exact (memLp_const (p := 2) (μ := weightedBallMeasure n) v).coeFn_toLp

/-- Evaluation of the transformed class is the pointwise C7 formula on its smooth representative. -/
theorem regularEvaluation_action (n : ℕ) (hn : 2 ≤ n) (g : Sp11)
    (f : WeakBallSpace n hn) (F : ℍ → BinaryForm n) (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) (q : ℍ) (hq : q ∈ Ball) :
    regularEvaluation n hn q hq (regularRepresentation n hn g f) = ballRepresentation n g F q :=
  regularEvaluation_eq_representative n hn q hq _
    (contDiffOn_ballRepresentation n hF g).continuousOn
    (weightedL2Action_ae_of_representative n hn g f.val F he)

/-- The origin is in the ball, with its fixed evaluation map. -/
def regularOrigin (n : ℕ) (hn : 2 ≤ n) : WeakBallSpace n hn →L[ℂ] BinaryForm n :=
  regularEvaluation n hn 0 (by simp [Ball, ballScale])

theorem ballAction_zero_eq_fullLift (n : ℕ) (a : QuaternionMatrix2) (F : ℍ → BinaryForm n) :
    ballAction n a F 0 = fullLift n F a := by
  simp [ballAction, mobiusDenominator, mobiusPoint, fullLift, groupOrigin]

/-- A nonzero regular vector has a translate with nonzero value at the origin.
The chosen inverse translate is the actual ball section at a nonvanishing point. -/
theorem regular_translate_detects (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) (hf : f ≠ 0) :
    ∃ g : Sp11, regularOrigin n hn (regularRepresentation n hn g f) ≠ 0 := by
  obtain ⟨F, hF, _, he⟩ := weakKernel_classicalRepresentative n hn f
  have hex : ∃ q ∈ Ball, F q ≠ 0 := by
    by_contra hx
    apply hf
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [he, ae_mem_ball n hn, Lp.coeFn_zero (E := BinaryForm n) (p := 2)
      (μ := weightedBallMeasure n)] with q heq hq hz
    change f.val q = (0 : BallL2 n) q
    rw [heq, hz]
    exact not_ne_iff.mp (fun hh => hx ⟨q, hq, hh⟩)
  obtain ⟨q, hq, hFq⟩ := hex
  let s : Sp11 := ⟨ballSection q, ballSection_isSp11 q hq⟩
  refine ⟨s⁻¹, ?_⟩
  rw [regularOrigin, regularEvaluation_action n hn s⁻¹ f F hF he]
  change ballAction n (signatureAdjoint (signatureAdjoint (ballSection q))) F 0 ≠ 0
  rw [signatureAdjoint_involutive, ballAction_zero_eq_fullLift, fullLift_section n F q hq]
  exact smul_ne_zero (ballWeight_pos _ hq).ne' hFq

theorem ballRepresentation_compact (n : ℕ) (a b : Fueter.UnitQuaternion)
    (F : ℍ → BinaryForm n) (q : ℍ) :
    ballRepresentation n (compactSp11 (a,b)) F q =
      polynomialRepresentation n (quaternionMatrix b) (F ((a:ℍ)⁻¹*q*b)) := by
  have ha : (a:ℍ)⁻¹ = star (a:ℍ) := by
    apply inv_eq_of_mul_eq_one_left
    exact Unitary.coe_star_mul_self a
  have hb : (star (b:ℍ))⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_left
    exact Unitary.coe_mul_star_self b
  simp [ballRepresentation, ballAction, compactSp11, compactMatrix, signatureAdjoint,
    mobiusDenominator, mobiusPoint, Quaternion.normSq_star, Fueter.unitQuaternion_normSq, ha, hb]

theorem regularAction_constant_compact (n : ℕ) (hn : 2 ≤ n) (a b : Fueter.UnitQuaternion)
    (v : BinaryForm n) :
    regularRepresentation n hn (compactSp11 (a,b)) (constantRegularIsometry n hn v) =
      constantRegularIsometry n hn (polynomialRepresentation n (quaternionMatrix b) v) := by
  apply regularEvaluation_ext n hn
  intro q hq
  have hc : ((constantRegularIsometry n hn v).val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n]
      (fun _ => v) := (memLp_const (p := 2) (μ := weightedBallMeasure n) v).coeFn_toLp
  calc
    _ = ballRepresentation n (compactSp11 (a,b)) (fun _ => v) q :=
      regularEvaluation_action n hn (compactSp11 (a,b)) (constantRegularIsometry n hn v)
        (fun _ => v) contDiffOn_const hc q hq
    _ = polynomialRepresentation n (quaternionMatrix b) v := ballRepresentation_compact n a b _ q
    _ = _ := (regularEvaluation_constant n hn q hq _).symm

end MathResearch.Spinor
