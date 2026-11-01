module
public import MathResearch.Spinor.CompactGroup

/-! The normalized quotient-Haar integration theorem needed by DS4, stated
as an explicit unverified background dependency. The assertion is for every
nonnegative continuous function on G, not for a chosen coefficient. It includes
integrability equivalence, so totalized integrals cannot conceal divergence. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion
open MeasureTheory
namespace MathResearch.Spinor

instance sp11ContinuousMul : ContinuousMul Sp11 := ⟨continuous_sp11_mul⟩
instance sp11ContinuousInv : ContinuousInv Sp11 where
  continuous_inv := Continuous.subtype_mk (continuous_signatureAdjoint.comp continuous_subtype_val) _
instance sp11TopologicalGroup : IsTopologicalGroup Sp11 where

/-- σ(q)k in G for q in the ball. The arbitrary outside value is never integrated. -/
def ballCompactPoint (q : ℍ) (k : CompactPair) : Sp11 := by
  classical
  exact if hq : q ∈ Ball then
    ⟨ballSection q * (compactSp11 k : QuaternionMatrix2),
      (ballSection_isSp11 q hq).mul (compactSp11 k).property⟩ else 1

@[simp] theorem ballCompactPoint_coe (q : ℍ) (hq : q ∈ Ball) (k : CompactPair) :
    (ballCompactPoint q k : QuaternionMatrix2) = ballSection q * (compactSp11 k : QuaternionMatrix2) := by
  simp [ballCompactPoint, hq]

def quotientHaarAverage (φ : Sp11 → ℝ) (q : ℍ) : ℝ :=
  (ballScale q)⁻¹ ^ 4 * ∫ k, φ (ballCompactPoint q k) ∂compactHaar

/-- The standard quotient integration formula in the stated normalization.
This structure is a theorem interface, not a proved theorem, instance or axiom.
Its proof must be developed separately; DS4 retains it as an explicit premise. -/
structure QuotientHaarIntegration (μG : Measure Sp11) : Prop where
  isHaar : μG.IsHaarMeasure
  integrable_iff : ∀ φ : Sp11 → ℝ, Continuous φ → (∀ g, 0 ≤ φ g) →
    (Integrable φ μG ↔ IntegrableOn (quotientHaarAverage φ) Ball volume)
  integral_formula : ∀ φ : Sp11 → ℝ, Continuous φ → (∀ g, 0 ≤ φ g) →
    (∫ g, φ g ∂μG) = ∫ q in Ball, quotientHaarAverage φ q

end MathResearch.Spinor
