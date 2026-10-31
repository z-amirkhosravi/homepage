module
public import MathResearch.Fueter.ZetaQuasiperiods

/-! Dilation of a real quaternionic lattice, using mathlib's lattice transport. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

/-- Multiplication by a nonzero real scalar as a continuous real linear equivalence. -/
def realDilation (a : ℝ) (ha : a ≠ 0) : ℍ ≃L[ℝ] ℍ :=
  (LinearEquiv.smulOfNeZero ℝ ℍ a ha).toContinuousLinearEquiv

@[simp] theorem realDilation_apply (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    realDilation a ha q = a • q := rfl

@[simp] theorem realDilation_symm_apply (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    (realDilation a ha).symm q = a⁻¹ • q := rfl

/-- The dilated lattice aL, represented by pullback under multiplication by a⁻¹. -/
def dilatedLattice (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) : Submodule ℤ ℍ :=
  ZLattice.comap ℝ L (realDilation a ha).symm.toLinearMap

instance (L : Submodule ℤ ℍ) [DiscreteTopology L] (a : ℝ) (ha : a ≠ 0) :
    DiscreteTopology (dilatedLattice L a ha) := by unfold dilatedLattice; infer_instance

instance (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : a ≠ 0) :
    IsZLattice ℝ (dilatedLattice L a ha) := by unfold dilatedLattice; infer_instance

/-- The definition is exactly the set of scalar multiples of lattice elements. -/
theorem mem_dilatedLattice (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    q ∈ dilatedLattice L a ha ↔ ∃ x ∈ L, a • x = q := by
  change a⁻¹ • q ∈ L ↔ _
  constructor
  · intro h
    exact ⟨a⁻¹ • q, h, by simp [smul_smul, ha]⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [smul_smul, ha] using hx

@[simp] theorem smul_mem_dilatedLattice (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    a • q ∈ dilatedLattice L a ha ↔ q ∈ L := by
  change a⁻¹ • (a • q) ∈ L ↔ _
  simp [smul_smul, ha]

/-- The bijection of all lattice indices, w ↦ aw. -/
def latticeDilationEquiv (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) :
    L ≃ₗ[ℤ] dilatedLattice L a ha :=
  ZLattice.comap_equiv ℝ L (realDilation a ha).symm.toLinearEquiv

@[simp] theorem latticeDilationEquiv_apply (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) (w : L) :
    (latticeDilationEquiv L a ha w : ℍ) = a • (w : ℍ) := rfl

/-- The same bijection restricts to the nonzero indices in the defining series. -/
def nonzeroLatticeDilationEquiv (L : Submodule ℤ ℍ) (a : ℝ) (ha : a ≠ 0) :
    {w : L // w ≠ 0} ≃ {w : dilatedLattice L a ha // w ≠ 0} :=
  (latticeDilationEquiv L a ha).toEquiv.subtypeEquiv (fun w => by simp)

end MathResearch.Fueter
