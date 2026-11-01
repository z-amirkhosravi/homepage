module
public import MathResearch.Fueter.ZetaQuasiperiods

/-! E4 and E5: zeta values and stationary elliptic functions at nonlattice half-periods. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
namespace MathResearch.Fueter

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- E4 version 1: the quasiperiod is twice the zeta value at a nonlattice half-period. -/
theorem E4_v1 (w : L) (hw : (2 : ℝ)⁻¹ • (w : ℍ) ∉ L) :
    zetaQuasiperiod L w = (2 : ℝ) • zeta L ((2 : ℝ)⁻¹ • (w : ℍ)) := by
  have hn : -((2 : ℝ)⁻¹ • (w : ℍ)) ∉ L := by simpa using hw
  have h := zeta_add L w hn
  have he : -((2 : ℝ)⁻¹ • (w : ℍ)) + (w : ℍ) = (2 : ℝ)⁻¹ • (w : ℍ) := by module
  rw [he, zeta_odd, sub_neg_eq_add, ← two_smul ℝ] at h
  exact h.symm

/-- The real differential of an even elliptic function is odd off the lattice. -/
theorem elliptic_fderiv_neg (j : Fin 3) {q : ℍ} (hq : q ∉ L) :
    fderiv ℝ (elliptic L j) (-q) = -fderiv ℝ (elliptic L j) q := by
  have hn : -q ∉ L := by simpa using hq
  have hd := ((elliptic_regular L j).1.contDiffAt
    ((isClosed_quaternionLattice L).isOpen_compl.mem_nhds hn)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp q (hasFDerivAt_id q).neg
  have he : (fun x => elliptic L j (-x)) = elliptic L j := funext (elliptic_even L j)
  have hf : -fderiv ℝ (elliptic L j) (-q) = fderiv ℝ (elliptic L j) q := by
    simpa [Function.comp_def, he] using h.fderiv.symm
  exact neg_eq_iff_eq_neg.mp hf

/-- The whole real Fréchet differential vanishes, not just its spatial coordinates. -/
theorem elliptic_fderiv_halfPeriod (j : Fin 3) (w : L)
    (hw : (2 : ℝ)⁻¹ • (w : ℍ) ∉ L) :
    fderiv ℝ (elliptic L j) ((2 : ℝ)⁻¹ • (w : ℍ)) = 0 := by
  have hn : -((2 : ℝ)⁻¹ • (w : ℍ)) ∉ L := by simpa using hw
  have he : -((2 : ℝ)⁻¹ • (w : ℍ)) + (w : ℍ) = (2 : ℝ)⁻¹ • (w : ℍ) := by module
  have h := elliptic_fderiv_add L j w hn
  rw [he, elliptic_fderiv_neg L j hw] at h
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun T : ℍ →L[ℝ] ℍ => T v) h
  have hz : (2 : ℝ) • (fderiv ℝ (elliptic L j) ((2 : ℝ)⁻¹ • (w : ℍ))) v = 0 := by
    rw [two_smul ℝ]
    exact eq_neg_iff_add_eq_zero.mp hv
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The stationary differential exists as an actual derivative. -/
theorem elliptic_hasFDerivAt_halfPeriod (j : Fin 3) (w : L)
    (hw : (2 : ℝ)⁻¹ • (w : ℍ) ∉ L) :
    HasFDerivAt (elliptic L j) (0 : ℍ →L[ℝ] ℍ) ((2 : ℝ)⁻¹ • (w : ℍ)) := by
  have hd := ((elliptic_regular L j).1.contDiffAt
    ((isClosed_quaternionLattice L).isOpen_compl.mem_nhds hw)).differentiableAt (by simp)
  simpa only [elliptic_fderiv_halfPeriod L j w hw] using hd.hasFDerivAt

/-- E5 version 1: the real derivative exists and every coordinate, including time, vanishes. -/
theorem E5_v1 (j : Fin 3) (w : L) (hw : (2 : ℝ)⁻¹ • (w : ℍ) ∉ L) :
    HasFDerivAt (elliptic L j) (0 : ℍ →L[ℝ] ℍ) ((2 : ℝ)⁻¹ • (w : ℍ)) ∧
    ∀ μ : Fin 4, coordPartial μ (elliptic L j) ((2 : ℝ)⁻¹ • (w : ℍ)) = 0 := by
  refine ⟨elliptic_hasFDerivAt_halfPeriod L j w hw, ?_⟩
  intro μ
  simp [coordPartial, directional, elliptic_fderiv_halfPeriod L j w hw]

end MathResearch.Fueter
