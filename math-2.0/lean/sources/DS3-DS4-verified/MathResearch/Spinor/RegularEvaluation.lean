module
public import MathResearch.Spinor.ClassicalWeak
public import Mathlib.MeasureTheory.Function.Holder

/-! Bounded point evaluation, obtained from the local smoothing formula and
mathlib's L² Hölder pairing. It is evaluation of the unique smooth representative,
not evaluation of an arbitrary almost-everywhere representative. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Distributions
open MeasureTheory ContinuousLinearMap
namespace MathResearch.Spinor

def weightedTestDensity (n : ℕ) (φ : BallTest) (q : ℍ) : ℂ := (φ q / ballDensity n q : ℝ)

theorem weightedTestDensity_tsupport (n : ℕ) (φ : BallTest) :
    tsupport (weightedTestDensity n φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  apply subset_tsupport
  intro h
  apply hq
  simp [weightedTestDensity, h]

theorem weightedTestDensity_continuous (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) :
    Continuous (weightedTestDensity n φ) := by
  apply ContinuousOn.continuous_of_tsupport_subset _ ball_isOpen
    ((weightedTestDensity_tsupport n φ).trans φ.tsupport_subset)
  exact Complex.continuous_ofReal.comp_continuousOn
    (φ.continuous.continuousOn.div (continuous_ballDensity n).continuousOn
      (fun q hq => (ballDensity_pos n hn hq).ne'))

theorem weightedTestDensity_memLp (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) :
    MemLp (weightedTestDensity n φ) 2 (weightedBallMeasure n) :=
  (weightedTestDensity_continuous n hn φ).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (weightedTestDensity_tsupport n φ))

/-- Testing against a compact smooth scalar function as a bounded complex-linear map. -/
def testIntegralCLM (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) : BallL2 n →L[ℂ] BinaryForm n :=
  (lsmul ℂ ℂ : ℂ →L[ℂ] BinaryForm n →L[ℂ] BinaryForm n).lpPairing (weightedBallMeasure n) 2 2
    ((weightedTestDensity_memLp n hn φ).toLp (weightedTestDensity n φ))

theorem testIntegralCLM_apply (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) (f : BallL2 n) :
    testIntegralCLM n hn φ f = ∫ q, φ q • f q := by
  rw [testIntegralCLM, lpPairing_eq_integral]
  have he : (∫ q, lsmul ℂ ℂ (((weightedTestDensity_memLp n hn φ).toLp (weightedTestDensity n φ)) q) (f q)
      ∂weightedBallMeasure n) = ∫ q, weightedTestDensity n φ q • f q ∂weightedBallMeasure n := by
    apply integral_congr_ae
    filter_upwards [(weightedTestDensity_memLp n hn φ).coeFn_toLp] with q hq
    rw [hq]
    rfl
  rw [he]
  change (∫ q, weightedTestDensity n φ q • f q
    ∂(volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_ballDensity n).measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ q in Ball, φ q • f q := by
      apply setIntegral_congr_fun ball_isOpen.measurableSet
      intro q hq
      dsimp only
      rw [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]
      change ballDensity n q • ((φ q / ballDensity n q : ℝ) • f q) = _
      rw [smul_smul]
      congr 1
      field_simp [(ballDensity_pos n hn hq).ne']
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by
      simp [φ.zero_on_compl hq]

/-- Point evaluation on the regular Hilbert space, with the smooth representative understood. -/
def regularEvaluation (n : ℕ) (hn : 2 ≤ n) (a : ℍ) (ha : a ∈ Ball) :
    WeakBallSpace n hn →L[ℂ] BinaryForm n :=
  (testIntegralCLM n hn (weylKernelTest ((1 - ‖a‖) / 4) a
    (by have := (mem_ball_iff a).mp ha; linarith)
    (by have := (mem_ball_iff a).mp ha; linarith))).comp (weakKernel n hn).subtypeL

theorem regularEvaluation_eq_weylRepresentative (n : ℕ) (hn : 2 ≤ n)
    (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace n hn) :
    regularEvaluation n hn a ha f = weylRepresentative (f.val : ℍ → BinaryForm n) a := by
  rw [regularEvaluation, ContinuousLinearMap.comp_apply, testIntegralCLM_apply]
  rfl

/-- Every continuous representative of a regular vector has this same evaluation. -/
theorem regularEvaluation_eq_representative (n : ℕ) (hn : 2 ≤ n)
    (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace n hn) {F : ℍ → BinaryForm n}
    (hF : ContinuousOn F Ball) (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    regularEvaluation n hn a ha f = F a := by
  rw [regularEvaluation_eq_weylRepresentative]
  have hW := smooth_harmonic_representative (ballL2_locallyIntegrableOn n hn f.val)
    (weakKernel_distributionLaplacian_zero n hn f)
  have hrep : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] weylRepresentative f.val :=
    (ae_weightedBall_iff n hn _).mpr hW.2.2
  exact continuousRepresentative_unique n hn hW.1.continuousOn hF (hrep.symm.trans he) ha

/-- The pointwise interior L² estimate, with a concrete bounded evaluation map. -/
theorem regularEvaluation_bound (n : ℕ) (hn : 2 ≤ n) (a : ℍ) (ha : a ∈ Ball)
    (f : WeakBallSpace n hn) :
    ‖weylRepresentative (f.val : ℍ → BinaryForm n) a‖ ≤ ‖regularEvaluation n hn a ha‖ * ‖f‖ := by
  rw [← regularEvaluation_eq_weylRepresentative n hn a ha f]
  exact (regularEvaluation n hn a ha).le_opNorm f

end MathResearch.Spinor
