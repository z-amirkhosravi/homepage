module
public import MathResearch.Spinor.CompactGroup

/-! Explicit, presently unverified background mean-value theorems.
These are precise theorem interfaces, not axioms and not instances. Research
results using them must retain the corresponding hypothesis. The standard
background proof belongs to a separate development and expository article. -/
@[expose] public section
noncomputable section
open scoped Quaternion ContDiff
open MeasureTheory InnerProductSpace
namespace MathResearch.Spinor

/-- The four-dimensional spherical mean-value theorem, expressed through Haar
probability on unit quaternions. It is not proved in this module. -/
def SphericalMeanValueOnBall : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    ∀ F : ℍ → E, ContDiffOn ℝ ∞ F Ball → HarmonicOnNhd F Ball →
      ∀ q ∈ Ball, (∫ a : Fueter.UnitQuaternion, F ((a:ℍ)⁻¹*q) ∂unitQuaternionHaar) = F 0

/-- The radial probability mean-value theorem on the ball, a standard corollary
of spherical mean values and polar integration. It is not proved here. -/
def RadialMeanValueOnBall : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    ∀ (n : ℕ), 2 ≤ n → ∀ F : ℍ → E,
      ContDiffOn ℝ ∞ F Ball → HarmonicOnNhd F Ball → Integrable F (weightedBallMeasure n) →
        (∫ q, F q ∂weightedBallMeasure n) = F 0

end MathResearch.Spinor
