module
public import MathResearch.Fueter.LatticeDilation

/-! E6: real dilation of elliptic functions, zeta, and the additive quasiperiod map. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

/-- The first real derivatives of the kernel have degree -4, including time. -/
theorem kernel_coordPartial_smul (μ : Fin 4) (a : ℝ) (ha : a ≠ 0)
    (q : ℍ) (hq : q ≠ 0) :
    coordPartial μ kernel (a • q) = (a ^ 4)⁻¹ • coordPartial μ kernel q := by
  simpa [iteratedPartial] using kernel_iteratedPartial_smul [μ] a ha q hq

theorem kernelSpatialPartial_smul (j : Fin 3) (a : ℝ) (ha : a ≠ 0)
    (q : ℍ) (hq : q ≠ 0) :
    kernelSpatialPartial j (a • q) = (a ^ 4)⁻¹ • kernelSpatialPartial j q :=
  kernel_coordPartial_smul j.succ a ha q hq

/-- Homogeneity of the complete real differential, as a continuous linear map. -/
theorem kernel_fderiv_smul (a : ℝ) (ha : a ≠ 0) (b : ℍ) (hb : b ≠ 0) :
    fderiv ℝ kernel (a • b) = (a ^ 4)⁻¹ • fderiv ℝ kernel b := by
  apply ContinuousLinearMap.ext
  intro q
  change fderiv ℝ kernel (a • b) q = (a ^ 4)⁻¹ • fderiv ℝ kernel b q
  rw [kernel_differential_coordinates, kernel_differential_coordinates, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro μ _
  rw [kernel_coordPartial_smul μ a ha b hb, smul_comm]

/-- Scaling the basepoint and the differential's argument gives the Taylor weight -3. -/
theorem kernel_fderiv_smul_apply (a : ℝ) (ha : a ≠ 0) (b : ℍ) (hb : b ≠ 0) (q : ℍ) :
    fderiv ℝ kernel (a • b) (a • q) = (a ^ 3)⁻¹ • fderiv ℝ kernel b q := by
  rw [map_smul, kernel_fderiv_smul a ha b hb]
  simp only [smul_apply, smul_smul]
  congr 1
  field_simp

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Reindex the convergent E-C1 brackets by the lattice dilation. -/
theorem elliptic_dilate (j : Fin 3) (a : ℝ) (ha : a ≠ 0) {q : ℍ} (hq : q ∉ L) :
    elliptic (dilatedLattice L a ha) j (a • q) = (a ^ 4)⁻¹ • elliptic L j q := by
  have hq0 : q ≠ 0 := fun h => hq (h ▸ L.zero_mem)
  unfold elliptic
  rw [← (nonzeroLatticeDilationEquiv L a ha).tsum_eq]
  change kernelSpatialPartial j (a • q) +
    (∑' b : {b : L // b ≠ 0}, (kernelSpatialPartial j (a • q + a • (b.1 : ℍ)) -
      kernelSpatialPartial j (a • (b.1 : ℍ)))) = _
  rw [kernelSpatialPartial_smul j a ha q hq0, smul_add, ← tsum_const_smul'']
  congr 1
  apply tsum_congr
  intro b
  have hb : (b.1 : ℍ) ≠ 0 := by simpa using b.2
  rw [← smul_add, kernelSpatialPartial_smul j a ha _ (add_lattice_ne_zero L b.1 hq),
    kernelSpatialPartial_smul j a ha _ hb, smul_sub]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Reindex intact E-C2 brackets; the differential scales in both its slots. -/
theorem zeta_dilate (a : ℝ) (ha : a ≠ 0) (q : ℍ) :
    zeta (dilatedLattice L a ha) (a • q) = (a ^ 3)⁻¹ • zeta L q := by
  unfold zeta
  rw [← (nonzeroLatticeDilationEquiv L a ha).tsum_eq]
  change kernel (a • q) +
    (∑' b : {b : L // b ≠ 0}, (kernel (a • q + a • (b.1 : ℍ)) -
      kernel (a • (b.1 : ℍ)) - fderiv ℝ kernel (a • (b.1 : ℍ)) (a • q))) = _
  rw [kernel_smul a ha q, smul_add, ← tsum_const_smul'']
  congr 1
  apply tsum_congr
  intro b
  have hb : (b.1 : ℍ) ≠ 0 := by simpa using b.2
  rw [← smul_add, kernel_smul a ha, kernel_smul a ha, kernel_fderiv_smul_apply a ha _ hb,
    smul_sub, smul_sub]

/-- Scaling the zeta increment scales the uniquely determined additive quasiperiod. -/
theorem zetaQuasiperiod_dilate (a : ℝ) (ha : a ≠ 0) (w : L) :
    zetaQuasiperiod (dilatedLattice L a ha) (latticeDilationEquiv L a ha w) =
      (a ^ 3)⁻¹ • zetaQuasiperiod L w := by
  have hq := zetaBasepoint_not_mem L
  have haq : a • zetaBasepoint L ∉ dilatedLattice L a ha := by simpa using hq
  calc
    _ = zeta (dilatedLattice L a ha)
          (a • zetaBasepoint L + (latticeDilationEquiv L a ha w : ℍ)) -
        zeta (dilatedLattice L a ha) (a • zetaBasepoint L) :=
      (zeta_add (dilatedLattice L a ha) (latticeDilationEquiv L a ha w) haq).symm
    _ = (a ^ 3)⁻¹ • (zeta L (zetaBasepoint L + (w : ℍ)) - zeta L (zetaBasepoint L)) := by
      rw [latticeDilationEquiv_apply, ← smul_add,
        zeta_dilate L a ha (zetaBasepoint L + (w : ℍ)), zeta_dilate L a ha (zetaBasepoint L), smul_sub]
    _ = _ := by rw [zeta_add L w hq]

/-- E6 version 1: all three real dilation identities for every positive scale. -/
theorem E6_v1 (a : ℝ) (ha : 0 < a) (j : Fin 3) (q : ℍ) (hq : q ∉ L) (w : L) :
    elliptic (dilatedLattice L a ha.ne') j (a • q) = (a ^ 4)⁻¹ • elliptic L j q ∧
    zeta (dilatedLattice L a ha.ne') (a • q) = (a ^ 3)⁻¹ • zeta L q ∧
    zetaQuasiperiod (dilatedLattice L a ha.ne') (latticeDilationEquiv L a ha.ne' w) =
      (a ^ 3)⁻¹ • zetaQuasiperiod L w :=
  ⟨elliptic_dilate L j a ha.ne' hq, zeta_dilate L a ha.ne' q,
    zetaQuasiperiod_dilate L a ha.ne' w⟩

end MathResearch.Fueter
