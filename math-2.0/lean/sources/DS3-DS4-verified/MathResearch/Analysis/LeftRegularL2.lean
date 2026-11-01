module
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Measure

/-! Left translation on L², constructed using mathlib's measure-preserving
pullback. This is infrastructure for a closed subrepresentation of L²(G). -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace MathResearch
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant]

def leftL2Translation (a : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun g => a⁻¹*g) (measurePreserving_mul_left μ a⁻¹)

theorem leftL2Translation_ae (a : G) (f : Lp ℂ 2 μ) :
    (leftL2Translation μ a f : G → ℂ) =ᵐ[μ] fun g => f (a⁻¹*g) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem leftL2Translation_mul (a b : G) (f : Lp ℂ 2 μ) :
    leftL2Translation μ (a*b) f = leftL2Translation μ a (leftL2Translation μ b f) := by
  apply Lp.ext
  filter_upwards [leftL2Translation_ae μ (a*b) f,
    leftL2Translation_ae μ a (leftL2Translation μ b f),
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae (leftL2Translation_ae μ b f)] with g hab ha hb
  rw [hab, ha, hb]
  simp [mul_assoc]

@[simp] theorem leftL2Translation_one (f : Lp ℂ 2 μ) : leftL2Translation μ 1 f = f := by
  apply Lp.ext
  simpa using leftL2Translation_ae μ 1 f

/-- The genuine unitary group homomorphism on Haar L². -/
def leftL2Representation : G →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun a :=
    { toLinearEquiv :=
        { toLinearMap := (leftL2Translation μ a).toLinearMap
          invFun := leftL2Translation μ a⁻¹
          left_inv := fun f => by
            change leftL2Translation μ a⁻¹ (leftL2Translation μ a f) = f
            rw [← leftL2Translation_mul, inv_mul_cancel, leftL2Translation_one]
          right_inv := fun f => by
            change leftL2Translation μ a (leftL2Translation μ a⁻¹ f) = f
            rw [← leftL2Translation_mul, mul_inv_cancel, leftL2Translation_one] }
      norm_map' := (leftL2Translation μ a).norm_map }
  map_one' := by ext f : 1; exact leftL2Translation_one μ f
  map_mul' a b := by ext f : 1; exact leftL2Translation_mul μ a b f

@[simp] theorem leftL2Representation_apply (a : G) (f : Lp ℂ 2 μ) :
    leftL2Representation μ a f = leftL2Translation μ a f := rfl

end MathResearch
