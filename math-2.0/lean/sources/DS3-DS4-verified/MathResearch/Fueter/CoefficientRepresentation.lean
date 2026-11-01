module
public import MathResearch.Fueter.KernelRotationAction
public import Mathlib.RepresentationTheory.Basic

/-! The coefficient action is a real representation and descends to the actual
special orthogonal group of quaternion space. -/
@[expose] public section
noncomputable section
open scoped Quaternion
namespace MathResearch.Fueter

/-- Right-H-linear functionals on the order-r derivative space. -/
abbrev CoefficientFunctional (r : ℕ) := kernelDerivativeSpace r →ₗ[ℍᵐᵒᵖ] ℍ

/-- The output factor is on the left; precomposition uses the inverse input action. -/
def coefficientSigmaLinear (r : ℕ) (k : QuaternionSpinPair) :
    CoefficientFunctional r →ₗ[ℝ] CoefficientFunctional r where
  toFun α :=
    { toFun := fun f => (k.2 : ℍ) * α (kernelRho r k⁻¹ f)
      map_add' f g := by simp only [map_add, mul_add]
      map_smul' c f := by
        simp only [map_smul, RingHom.id_apply]
        change (k.2 : ℍ) * (α (kernelRho r k⁻¹ f) * c.unop) =
          ((k.2 : ℍ) * α (kernelRho r k⁻¹ f)) * c.unop
        exact (mul_assoc _ _ _).symm }
  map_add' α β := by
    apply LinearMap.ext
    intro f
    exact mul_add _ _ _
  map_smul' t α := by
    apply LinearMap.ext
    intro f
    change (k.2 : ℍ) * (t • α (kernelRho r k⁻¹ f)) = t • ((k.2 : ℍ) * α (kernelRho r k⁻¹ f))
    simp only [mul_smul_comm]

@[simp] theorem coefficientSigmaLinear_apply (r : ℕ) (k : QuaternionSpinPair)
    (α : CoefficientFunctional r) (f : kernelDerivativeSpace r) :
    coefficientSigmaLinear r k α f = (k.2 : ℍ) * α (kernelRho r k⁻¹ f) := rfl

@[simp] theorem coefficientSigmaLinear_one (r : ℕ) :
    coefficientSigmaLinear r 1 = LinearMap.id := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro f
  simp

theorem coefficientSigmaLinear_mul (r : ℕ) (k l : QuaternionSpinPair) (α : CoefficientFunctional r) :
    coefficientSigmaLinear r (k * l) α = coefficientSigmaLinear r k (coefficientSigmaLinear r l α) := by
  apply LinearMap.ext
  intro f
  simp only [coefficientSigmaLinear_apply, mul_inv_rev, kernelRho_mul,
    LinearEquiv.mul_apply, Prod.snd_mul, Submonoid.coe_mul, mul_assoc]

/-- Each coefficient transformation is an invertible real linear map. -/
def coefficientSigma (r : ℕ) (k : QuaternionSpinPair) :
    CoefficientFunctional r ≃ₗ[ℝ] CoefficientFunctional r where
  __ := coefficientSigmaLinear r k
  invFun := coefficientSigmaLinear r k⁻¹
  left_inv α := by
    change coefficientSigmaLinear r k⁻¹ (coefficientSigmaLinear r k α) = α
    rw [← coefficientSigmaLinear_mul, inv_mul_cancel, coefficientSigmaLinear_one]
    rfl
  right_inv α := by
    change coefficientSigmaLinear r k (coefficientSigmaLinear r k⁻¹ α) = α
    rw [← coefficientSigmaLinear_mul, mul_inv_cancel, coefficientSigmaLinear_one]
    rfl

/-- The composition order in EI7 is the ordinary, forward group law. -/
def coefficientSigmaHom (r : ℕ) : QuaternionSpinPair →*
    (CoefficientFunctional r ≃ₗ[ℝ] CoefficientFunctional r) where
  toFun := coefficientSigma r
  map_one' := LinearEquiv.toLinearMap_injective (coefficientSigmaLinear_one r)
  map_mul' k l := by
    apply LinearEquiv.ext
    intro α
    exact coefficientSigmaLinear_mul r k l α

/-- Mathlib's `Representation` formulation of the spin action. -/
def coefficientSpinRepresentation (r : ℕ) : Representation ℝ QuaternionSpinPair (CoefficientFunctional r) where
  toFun := coefficientSigmaLinear r
  map_one' := coefficientSigmaLinear_one r
  map_mul' k l := LinearMap.ext (coefficientSigmaLinear_mul r k l)

/-- The two minus signs cancel on right-linear functionals. -/
theorem coefficientSigma_central (r : ℕ) : coefficientSigma r (-1, -1) = 1 := by
  apply LinearEquiv.ext
  intro α
  apply LinearMap.ext
  intro f
  change (-1 : ℍ) * α (kernelRho r ((-1, -1) : QuaternionSpinPair)⁻¹ f) = α f
  have hi : ((-1, -1) : QuaternionSpinPair)⁻¹ = (-1, -1) := by
    apply Prod.ext <;> apply Subtype.ext <;> change star (-1 : ℍ) = -1 <;> simp
  rw [hi, kernelRho_central, map_neg α]
  simp

theorem coefficientSigma_kills_cover_kernel (r : ℕ) :
    quaternionSpinCover.ker ≤ (coefficientSigmaHom r).ker := by
  intro k hk
  have hk' : quaternionRotation k = 1 := congrArg Subtype.val hk
  rcases quaternionRotation_kernel k hk' with rfl | rfl
  · exact (coefficientSigmaHom r).map_one
  · exact coefficientSigma_central r

/-- Descent to determinant-one real isometries, using the proved surjectivity of the spin cover. -/
def coefficientSO4Action (r : ℕ) : QuaternionSO4 →*
    (CoefficientFunctional r ≃ₗ[ℝ] CoefficientFunctional r) :=
  quaternionSpinCover.liftOfSurjective quaternionSpinCover_surjective
    ⟨coefficientSigmaHom r, coefficientSigma_kills_cover_kernel r⟩

@[simp] theorem coefficientSO4Action_lift (r : ℕ) (k : QuaternionSpinPair) :
    coefficientSO4Action r (quaternionSpinCover k) = coefficientSigma r k := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ k

/-- Mathlib's real representation of the actual rotation group. -/
def coefficientSO4Representation (r : ℕ) : Representation ℝ QuaternionSO4 (CoefficientFunctional r) where
  toFun e := (coefficientSO4Action r e).toLinearMap
  map_one' := congrArg LinearEquiv.toLinearMap (map_one (coefficientSO4Action r))
  map_mul' e e' := congrArg LinearEquiv.toLinearMap (map_mul (coefficientSO4Action r) e e')

@[simp] theorem coefficientSO4Representation_lift (r : ℕ) (k : QuaternionSpinPair) :
    coefficientSO4Representation r (quaternionSpinCover k) = coefficientSpinRepresentation r k :=
  congrArg LinearEquiv.toLinearMap (coefficientSO4Action_lift r k)

end MathResearch.Fueter
