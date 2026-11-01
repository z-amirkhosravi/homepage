module
public import MathResearch.Analysis.HarmonicPartials
public import MathResearch.Spinor.RegularEvaluation

/-! Every finite real directional derivative at an interior point is a bounded
linear functional of the regular Hilbert vector. Consequently all these
derivatives commute with Bochner averaging of integrable families of vectors. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Distributions
open MeasureTheory
namespace MathResearch.Spinor

def interiorKernelTest (a : ℍ) (ha : a ∈ Ball) : BallTest :=
  weylKernelTest ((1-‖a‖)/4) a
    (by have := (mem_ball_iff a).mp ha; linarith)
    (by have := (mem_ball_iff a).mp ha; linarith)

/-- The actual signed differentiated smoothing test defines an all-order evaluation map. -/
def regularPartialEvaluation (n : ℕ) (hn : 2 ≤ n) (vs : List ℍ) (a : ℍ) (ha : a ∈ Ball) :
    WeakBallSpace n hn →L[ℂ] BinaryForm n :=
  (testIntegralCLM n hn (partialAdjointTest vs (interiorKernelTest a ha))).comp (weakKernel n hn).subtypeL

theorem testIntegralCLM_eq_representative (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (f : BallL2 n) {F : ℍ → BinaryForm n} (he : (f : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    testIntegralCLM n hn φ f = ∫ q, φ q • F q := by
  rw [testIntegralCLM_apply]
  have h := (ae_restrict_iff' ball_isOpen.measurableSet).mp ((ae_weightedBall_iff n hn _).mp he)
  apply integral_congr_ae
  filter_upwards [h] with q hq
  by_cases hb : q ∈ Ball
  · rw [hq hb]
  · simp [φ.zero_on_compl hb]

/-- Equality with genuine derivatives of every smooth representative. -/
theorem regularPartialEvaluation_eq_representative (n : ℕ) (hn : 2 ≤ n)
    (vs : List ℍ) (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace n hn)
    {F : ℍ → BinaryForm n} (hF : ContDiffOn ℝ ∞ F Ball)
    (he : (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] F) :
    regularPartialEvaluation n hn vs a ha f = realDirectionalPartials vs F a := by
  have hΔ : distributionLaplacian (Distribution.ofFun ballOpen F volume ⊤) = 0 := by
    have hd : spinorDistribution n f.val = Distribution.ofFun ballOpen F volume ⊤ :=
      Distribution.ofFun_congr_ae ((ae_weightedBall_iff n hn _).mp he)
    rw [← hd]
    exact weakKernel_distributionLaplacian_zero n hn f
  change testIntegralCLM n hn (partialAdjointTest vs (interiorKernelTest a ha)) f.val = _
  rw [testIntegralCLM_eq_representative n hn _ f.val he]
  exact (harmonicPartials_test_formula hF hΔ vs
    (by have := (mem_ball_iff a).mp ha; linarith)
    (by have := (mem_ball_iff a).mp ha; linarith)).symm

theorem regularPartialEvaluation_eq_weylRepresentative (n : ℕ) (hn : 2 ≤ n)
    (vs : List ℍ) (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace n hn) :
    regularPartialEvaluation n hn vs a ha f =
      realDirectionalPartials vs (weylRepresentative (f.val : ℍ → BinaryForm n)) a := by
  have hW := smooth_harmonic_representative (ballL2_locallyIntegrableOn n hn f.val)
    (weakKernel_distributionLaplacian_zero n hn f)
  exact regularPartialEvaluation_eq_representative n hn vs a ha f hW.1
    ((ae_weightedBall_iff n hn _).mpr hW.2.2)

/-- Interior L² estimates for every finite list of real directions, including order zero. -/
theorem regularPartials_bound (n : ℕ) (hn : 2 ≤ n) (vs : List ℍ)
    (a : ℍ) (ha : a ∈ Ball) (f : WeakBallSpace n hn) :
    ‖realDirectionalPartials vs (weylRepresentative (f.val : ℍ → BinaryForm n)) a‖ ≤
      ‖regularPartialEvaluation n hn vs a ha‖ * ‖f‖ := by
  rw [← regularPartialEvaluation_eq_weylRepresentative]
  exact (regularPartialEvaluation n hn vs a ha).le_opNorm f

/-- All-order differentiation commutes with Hilbert-space averaging.
The family is assumed Bochner integrable, not merely pointwise integrable. -/
theorem regularPartials_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (n : ℕ) (hn : 2 ≤ n) (vs : List ℍ) (a : ℍ) (ha : a ∈ Ball)
    {f : X → WeakBallSpace n hn} (hf : Integrable f μ) :
    realDirectionalPartials vs (weylRepresentative ((∫ x, f x ∂μ).val : ℍ → BinaryForm n)) a =
      ∫ x, realDirectionalPartials vs (weylRepresentative ((f x).val : ℍ → BinaryForm n)) a ∂μ := by
  simp_rw [← regularPartialEvaluation_eq_weylRepresentative n hn vs a ha]
  exact ((regularPartialEvaluation n hn vs a ha).integral_comp_comm hf).symm

end MathResearch.Spinor
