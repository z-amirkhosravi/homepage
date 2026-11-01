module
public import MathResearch.Spinor.WeylRegularity

/-! Arbitrary finite strings of real directional derivatives preserve smooth
weak harmonicity. Integration by parts moves each derivative onto an actual
compactly supported test; the Weyl smoothing identity then estimates it. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ContDiff Distributions
open MeasureTheory
namespace MathResearch.Spinor

theorem testLaplacian_directional (v : ℍ) (φ : BallTest) :
    testLaplacian (testDirectional v φ) = testDirectional v (testLaplacian φ) := by
  simp only [testLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [testDirectional_comm _ v, testDirectional_comm _ v]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem distributionLaplacian_directional (v : ℍ) (T : 𝓓'(ballOpen, E)) :
    distributionLaplacian (Distribution.lineDerivCLM v T) =
      Distribution.lineDerivCLM v (distributionLaplacian T) := by
  ext φ : 1
  simp only [distributionLaplacian_apply, Distribution.lineDerivCLM_apply]
  change -T (testDirectional v (testLaplacian φ)) = -T (testLaplacian (testDirectional v φ))
  rw [testLaplacian_directional]

/-- Outer derivatives are listed first; each direction is an arbitrary real quaternion vector. -/
def realDirectionalPartials : List ℍ → (ℍ → E) → ℍ → E
  | [], u => u
  | v :: vs, u => fun a => fderiv ℝ (realDirectionalPartials vs u) a v

theorem contDiffOn_realDirectionalPartials {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball) (vs : List ℍ) :
    ContDiffOn ℝ ∞ (realDirectionalPartials vs u) Ball := by
  induction vs with
  | nil => exact hu
  | cons v vs ih => exact contDiffOn_directional ih v

theorem distributionLaplacian_realDirectionalPartials {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) (vs : List ℍ) :
    distributionLaplacian (Distribution.ofFun ballOpen (realDirectionalPartials vs u) volume ⊤) = 0 := by
  induction vs with
  | nil => exact hΔ
  | cons v vs ih =>
    change distributionLaplacian (Distribution.ofFun ballOpen
      (fun a => fderiv ℝ (realDirectionalPartials vs u) a v) volume ⊤) = 0
    rw [← distribution_directional_of_smooth (contDiffOn_realDirectionalPartials hu vs),
      distributionLaplacian_directional, ih, map_zero]

/-- The signed adjoint test, with reversal of derivative order implemented recursively. -/
def partialAdjointTest : List ℍ → BallTest → BallTest
  | [], φ => φ
  | v :: vs, φ => partialAdjointTest vs (-testDirectional v φ)

theorem integral_test_realDirectionalPartials {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball) (vs : List ℍ) (φ : BallTest) :
    (∫ a, φ a • realDirectionalPartials vs u a) = ∫ a, partialAdjointTest vs φ a • u a := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    change (∫ a, φ a • fderiv ℝ (realDirectionalPartials vs u) a v) = _
    rw [integral_test_directional (contDiffOn_realDirectionalPartials hu vs)]
    have h := ih (-testDirectional v φ)
    simpa only [partialAdjointTest, FunLike.coe_neg, Pi.neg_apply, neg_smul, integral_neg] using h

variable [CompleteSpace E]

/-- The local smoothing formula holds pointwise for every smooth harmonic function. -/
theorem smooth_harmonic_kernel_formula {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    {a : ℍ} {r : ℝ} (hr : 0 < r) (ha : ‖a‖ + 2*r < 1) :
    u a = weylSmooth r u a := by
  have hi := hu.continuousOn.locallyIntegrableOn (μ := volume) ball_isOpen.measurableSet
  have hW := smooth_harmonic_representative hi hΔ
  have he := Measure.eqOn_open_of_ae_eq hW.2.2 ball_isOpen hu.continuousOn hW.1.continuousOn
  rw [he ((mem_ball_iff a).mpr (by linarith))]
  exact weylRepresentative_eq_smooth hi hΔ hr ha

/-- All-order interior derivative formula; no differentiation of an L² representative occurs. -/
theorem harmonicPartials_test_formula {u : ℍ → E}
    (hu : ContDiffOn ℝ ∞ u Ball)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0)
    (vs : List ℍ) {a : ℍ} {r : ℝ} (hr : 0 < r) (ha : ‖a‖ + 2*r < 1) :
    realDirectionalPartials vs u a = ∫ y, partialAdjointTest vs (weylKernelTest r a hr ha) y • u y := by
  rw [smooth_harmonic_kernel_formula (contDiffOn_realDirectionalPartials hu vs)
    (distributionLaplacian_realDirectionalPartials hu hΔ vs) hr ha]
  exact integral_test_realDirectionalPartials hu vs (weylKernelTest r a hr ha)

end MathResearch.Spinor
