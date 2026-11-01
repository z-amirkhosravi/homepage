module
public import MathResearch.Spinor.WeightedFueter
public import MathResearch.Fueter.QuaternionRotations

/-! Invariance of real bilinear contraction under a change of orthonormal frame. -/
@[expose] public section
noncomputable section
open scoped Quaternion BigOperators
namespace MathResearch.Spinor

def quaternionONB : OrthonormalBasis (Fin 4) ℝ ℍ :=
  Fueter.coordinateBasis.toOrthonormalBasis (by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Fueter.coordinateBasis_eq, Quaternion.inner_def]
    fin_cases i <;> fin_cases j <;> norm_num)

@[simp] theorem quaternionONB_apply (i : Fin 4) : quaternionONB i = Fueter.coordinateBasis i := by
  simp [quaternionONB, Module.Basis.coe_toOrthonormalBasis]

theorem orthonormal_bilinear_contraction {W : Type*} [AddCommGroup W] [Module ℝ W]
    (b c : OrthonormalBasis (Fin 4) ℝ ℍ) (B : ℍ →ₗ[ℝ] ℍ →ₗ[ℝ] W) :
    ∑ i, B (c i) (c i) = ∑ j, B (b j) (b j) := by
  have he (x y : ℍ) : B x y =
      ∑ j, ∑ k, (inner ℝ (b j) x * inner ℝ (b k) y) • B (b j) (b k) := by
    conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
  simp_rw [he (c _) (c _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hi (k : Fin 4) :
      (∑ i, inner ℝ (b j) (c i) * inner ℝ (b k) (c i)) = if j = k then 1 else 0 := by
    simpa only [real_inner_comm (b k), b.inner_eq_ite, eq_comm] using
      c.sum_inner_mul_inner (b j) (b k)
  simp [hi]

/-- In particular the ordered real quaternion basis may be rotated before contraction. -/
theorem quaternion_contraction_rotation {W : Type*} [AddCommGroup W] [Module ℝ W]
    (R : ℍ ≃ₗᵢ[ℝ] ℍ) (B : ℍ →ₗ[ℝ] ℍ →ₗ[ℝ] W) :
    ∑ i : Fin 4, B (R (Fueter.coordinateBasis i)) (R (Fueter.coordinateBasis i)) =
      ∑ i : Fin 4, B (Fueter.coordinateBasis i) (Fueter.coordinateBasis i) := by
  simpa using orthonormal_bilinear_contraction quaternionONB (quaternionONB.map R) B

end MathResearch.Spinor
