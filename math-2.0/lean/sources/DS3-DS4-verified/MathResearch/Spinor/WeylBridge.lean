module
public import MathResearch.Spinor.WeakHarmonic

/-! The exact remaining Weyl input and its application in the written DS2
argument. The input is an explicit proposition, not an axiom or an instance.
No declaration here proves Weyl's lemma. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion Distributions ContDiff
open MeasureTheory InnerProductSpace
namespace MathResearch.Spinor

/-- General local Weyl regularity on the quaternionic Euclidean ball.
This is a missing analytic theorem, with no Fueter equation or weighted space
in its assumptions. Supplying a value of this proposition is still required. -/
def WeylRegularityOnBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ u : ℍ → E, LocallyIntegrableOn u Ball volume →
    distributionLaplacian (Distribution.ofFun ballOpen u volume ⊤) = 0 →
    ∃ v : ℍ → E, ContDiffOn ℝ ∞ v Ball ∧ HarmonicOnNhd v Ball ∧
      u =ᵐ[volume.restrict Ball] v

/-- DS2's Weyl step, conditional only on the displayed general Laplace-regularity
input. Weak harmonicity is proved, not assumed of the Fueter solution. -/
theorem weakKernel_smoothRepresentative_of_weyl (n : ℕ) (hn : 2 ≤ n)
    (hW : WeylRegularityOnBall (BinaryForm n)) (f : WeakBallSpace n hn) :
    ∃ v : ℍ → BinaryForm n, ContDiffOn ℝ ∞ v Ball ∧ HarmonicOnNhd v Ball ∧
      (f.val : ℍ → BinaryForm n) =ᵐ[weightedBallMeasure n] v := by
  obtain ⟨v, hv, hH, he⟩ := hW f.val (ballL2_locallyIntegrableOn n hn f.val)
    (weakKernel_distributionLaplacian_zero n hn f)
  exact ⟨v, hv, hH, (ae_weightedBall_iff n hn _).mpr he⟩

/-- Smooth representatives are unique on B, not outside B where the measure vanishes. -/
theorem continuousRepresentative_unique (n : ℕ) (hn : 2 ≤ n)
    {u v : ℍ → BinaryForm n} (hu : ContinuousOn u Ball) (hv : ContinuousOn v Ball)
    (he : u =ᵐ[weightedBallMeasure n] v) : Set.EqOn u v Ball :=
  Measure.eqOn_open_of_ae_eq ((ae_weightedBall_iff n hn _).mp he) ball_isOpen hu hv

/-- Every real continuous linear coefficient of a harmonic spinor is harmonic. -/
theorem harmonicRepresentative_coefficient (n : ℕ) {v : ℍ → BinaryForm n}
    (hv : HarmonicOnNhd v Ball) (L : BinaryForm n →L[ℝ] ℝ) :
    HarmonicOnNhd (fun q => L (v q)) Ball := hv.comp_CLM L

end MathResearch.Spinor
