module
public import MathResearch.Fueter.CoefficientRepresentation
public import MathResearch.Fueter.LatticeDilation

/-! Absolute coefficient functionals and EI7's lattice rotation covariance. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

/-- The actual rotated lattice eL, transported using mathlib's lattice construction. -/
def rotatedLattice (L : Submodule ℤ ℍ) (e : ℍ ≃ₗᵢ[ℝ] ℍ) : Submodule ℤ ℍ :=
  ZLattice.comap ℝ L e.toContinuousLinearEquiv.symm.toLinearMap

instance (L : Submodule ℤ ℍ) [DiscreteTopology L] (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    DiscreteTopology (rotatedLattice L e) := by unfold rotatedLattice; infer_instance

instance (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    IsZLattice ℝ (rotatedLattice L e) := by unfold rotatedLattice; infer_instance

theorem mem_rotatedLattice (L : Submodule ℤ ℍ) (e : ℍ ≃ₗᵢ[ℝ] ℍ) (q : ℍ) :
    q ∈ rotatedLattice L e ↔ ∃ x ∈ L, e x = q := by
  change e.symm q ∈ L ↔ _
  constructor
  · intro h
    exact ⟨e.symm q, h, e.apply_symm_apply q⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [e.symm_apply_apply] using hx

def latticeRotationEquiv (L : Submodule ℤ ℍ) (e : ℍ ≃ₗᵢ[ℝ] ℍ) : L ≃ₗ[ℤ] rotatedLattice L e :=
  ZLattice.comap_equiv ℝ L e.toContinuousLinearEquiv.symm.toLinearEquiv

@[simp] theorem latticeRotationEquiv_apply (L : Submodule ℤ ℍ) (e : ℍ ≃ₗᵢ[ℝ] ℍ) (w : L) :
    (latticeRotationEquiv L e w : ℍ) = e (w : ℍ) := rfl

def nonzeroLatticeRotationEquiv (L : Submodule ℤ ℍ) (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    {w : L // w ≠ 0} ≃ {w : rotatedLattice L e // w ≠ 0} :=
  (latticeRotationEquiv L e).toEquiv.subtypeEquiv (fun w => by simp)

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- N2 extends by finite right-linear combinations to the whole derivative space. -/
theorem summable_norm_kernelDerivativeSpace {r : ℕ} (hr : 2 ≤ r) {f : SmoothPunctured}
    (hf : f ∈ kernelDerivativeSpace r) :
    Summable (fun w : {w : L // w ≠ 0} => ‖f (w.1 : ℍ)‖) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    change x ∈ Set.range (fun ν : {ν : Fin 3 → ℕ // ∑ j, ν j = r} => smoothHigherKernel ν) at hx
    obtain ⟨⟨ν, hν⟩, rfl⟩ := hx
    have hn (w : {w : L // w ≠ 0}) : (w.1 : ℍ) ≠ 0 := by simpa using w.2
    simpa only [smoothHigherKernel_apply _ (hn _)] using summable_norm_eisenstein L ν (by omega)
  | zero => simp
  | add f g _ _ hf hg =>
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun w => norm_add_le (f (w.1 : ℍ)) (g (w.1 : ℍ))) (hf.add hg)
  | smul c f _ hf =>
    simpa only [smoothPunctured_smul_apply, norm_mul] using hf.mul_right ‖c.unop‖

/-- The defining absolutely convergent lattice sum, as a right-H-linear functional. -/
def latticeCoefficientFunctional (r : ℕ) (hr : 2 ≤ r) : CoefficientFunctional r where
  toFun f := ∑' w : {w : L // w ≠ 0}, (f : SmoothPunctured) (w.1 : ℍ)
  map_add' f g := by
    exact (summable_norm_kernelDerivativeSpace L hr f.property).of_norm.tsum_add
      (summable_norm_kernelDerivativeSpace L hr g.property).of_norm
  map_smul' c f := by
    exact tsum_mul_right

/-- The functional's values on generators are precisely the earlier Eisenstein coefficients. -/
theorem latticeCoefficientFunctional_generator (ν : Fin 3 → ℕ) (hν : 2 ≤ ∑ j, ν j) :
    latticeCoefficientFunctional L (∑ j, ν j) hν ⟨smoothHigherKernel ν, smoothHigherKernel_mem ν⟩ =
      eisensteinCoefficient L ν := by
  apply tsum_congr
  intro w
  exact smoothHigherKernel_apply ν (by simpa using w.2)

/-- Reindexing under a bijective real rotation is valid for the actual lattice sums. -/
theorem latticeCoefficientFunctional_rotated (r : ℕ) (hr : 2 ≤ r)
    (e : ℍ ≃ₗᵢ[ℝ] ℍ) (f : kernelDerivativeSpace r) :
    latticeCoefficientFunctional (rotatedLattice L e) r hr f =
      ∑' w : {w : L // w ≠ 0}, (f : SmoothPunctured) (e (w.1 : ℍ)) := by
  exact ((nonzeroLatticeRotationEquiv L e).tsum_eq
    (fun w : {w : rotatedLattice L e // w ≠ 0} => (f : SmoothPunctured) (w.1 : ℍ))).symm

/-- EI7's displayed covariance identity, with the forward lattice rotation aLb⁻¹. -/
theorem coefficient_rotation_covariance (r : ℕ) (hr : 2 ≤ r) (k : QuaternionSpinPair) :
    latticeCoefficientFunctional (rotatedLattice L (quaternionRotation k)) r hr =
      coefficientSigma r k (latticeCoefficientFunctional L r hr) := by
  apply LinearMap.ext
  intro f
  rw [latticeCoefficientFunctional_rotated]
  change (∑' w : {w : L // w ≠ 0}, (f : SmoothPunctured) (quaternionRotation k (w.1 : ℍ))) =
    (k.2 : ℍ) * ∑' w : {w : L // w ≠ 0},
      (kernelRho r k⁻¹ f : SmoothPunctured) (w.1 : ℍ)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro w
  change _ = (k.2 : ℍ) * ((k⁻¹.2 : ℍ) * (f : SmoothPunctured) (quaternionRotation (k⁻¹)⁻¹ (w.1 : ℍ)))
  simp only [inv_inv, Prod.snd_inv, unitQuaternion_coe_inv, ← mul_assoc,
    ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul]

/-- The same covariance is intrinsic to SO(4), independent of a spin lift. -/
theorem coefficient_SO4_covariance (r : ℕ) (hr : 2 ≤ r) (e : QuaternionSO4) :
    latticeCoefficientFunctional (rotatedLattice L e.val) r hr =
      coefficientSO4Action r e (latticeCoefficientFunctional L r hr) := by
  obtain ⟨k, rfl⟩ := quaternionSpinCover_surjective e
  rw [coefficientSO4Action_lift]
  exact coefficient_rotation_covariance L r hr k

/-- EI7/v1: invariant right-H derivative space; absolutely convergent, right-H-linear
coefficient functionals; the genuine real spin representation; covariance; and
factorization through the actual determinant-one rotation group. -/
theorem EI7_v1 (r : ℕ) (hr : 1 < r) :
    (∀ k : QuaternionSpinPair, ∀ f ∈ kernelDerivativeSpace r,
      smoothRho k f ∈ kernelDerivativeSpace r) ∧
    (∀ f : kernelDerivativeSpace r,
      Summable (fun w : {w : L // w ≠ 0} => ‖(f : SmoothPunctured) (w.1 : ℍ)‖)) ∧
    (∀ k : QuaternionSpinPair,
      latticeCoefficientFunctional (rotatedLattice L (quaternionRotation k)) r hr =
        coefficientSpinRepresentation r k (latticeCoefficientFunctional L r hr)) ∧
    (∀ k : QuaternionSpinPair,
      coefficientSO4Representation r (quaternionSpinCover k) = coefficientSpinRepresentation r k) ∧
    (∀ e : QuaternionSO4,
      latticeCoefficientFunctional (rotatedLattice L e.val) r hr =
        coefficientSO4Representation r e (latticeCoefficientFunctional L r hr)) := by
  exact ⟨smoothRho_mem r, fun f => summable_norm_kernelDerivativeSpace L hr f.property,
    coefficient_rotation_covariance L r hr, coefficientSO4Representation_lift r,
    coefficient_SO4_covariance L r hr⟩

end MathResearch.Fueter
