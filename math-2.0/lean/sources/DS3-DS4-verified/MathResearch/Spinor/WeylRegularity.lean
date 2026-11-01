module
public import MathResearch.Analysis.WeylRepresentative
public import MathResearch.Analysis.SmoothDistribution
public import MathResearch.Spinor.WeylBridge

/-! Weyl's lemma on the quaternionic ball, now proved without an external
regularity assumption. The proof constructs normalized signed kernels from
an explicit regularized Newton potential and uses mathlib Lebesgue differentiation. -/
@[expose] public section
noncomputable section
open scoped Quaternion ContDiff Distributions
open MeasureTheory InnerProductSpace
namespace MathResearch.Spinor

/-- Weyl regularity for functions with values in any complete real normed space. -/
theorem smooth_harmonic_representative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {u : ℍ → E}
    (hu : LocallyIntegrableOn u Ball volume)
    (hΔ : distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0) :
    ContDiffOn ℝ ∞ (weylRepresentative u) Ball ∧
      HarmonicOnNhd (weylRepresentative u) Ball ∧
      u =ᵐ[volume.restrict Ball] weylRepresentative u := by
  have hs := contDiffOn_weylRepresentative hu hΔ
  have he := ae_weylRepresentative hu hΔ
  refine ⟨hs, harmonicOnNhd_of_smooth_distributionLaplacian_zero hs ?_, he⟩
  rw [← Distribution.ofFun_congr_ae he]
  exact hΔ

/-- Discharges the exact Weyl premise retained in the preceding DS2 release. -/
theorem weylRegularityOnBall (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : WeylRegularityOnBall E := by
  intro u hu hΔ
  exact ⟨weylRepresentative u, smooth_harmonic_representative hu hΔ⟩

/-- The smooth harmonic representative in the canonical DS2 argument is
unconditional: conjugate Fueter factorization followed by the proved Weyl lemma. -/
theorem weakKernel_smoothRepresentative (n : ℕ) (hn : 2 ≤ n) (f : WeakBallSpace n hn) :
    ∃ v : ℍ → BinaryForm n, ContDiffOn ℝ ∞ v Ball ∧ HarmonicOnNhd v Ball ∧
      (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] v :=
  weakKernel_smoothRepresentative_of_weyl n hn (weylRegularityOnBall _) f

end MathResearch.Spinor
