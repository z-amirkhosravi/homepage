module
public import MathResearch.Spinor.FullLift

/-! A concrete nonzero curvature action in every positive polynomial degree. -/
@[expose] public section
noncomputable section
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
open MvPolynomial
namespace MathResearch.Spinor

theorem curvature_origin_action (m : ℕ) :
    infinitesimal (quaternionMatrix (ballCurvature 0 1 (⟨0,1,0,0⟩ : ℍ))) (X 0 ^ (m+1)) =
      C (-2 * Complex.I * (m+1 : ℂ)) * X 0 ^ (m+1) := by
  rw [ballCurvature_origin]
  simp [infinitesimal, substitution, quaternionMatrix, pderiv_X]
  ring

theorem curvature_origin_action_ne_zero (m : ℕ) :
    infinitesimal (quaternionMatrix (ballCurvature 0 1 (⟨0,1,0,0⟩ : ℍ))) (X 0 ^ (m+1)) ≠ 0 := by
  rw [curvature_origin_action]
  apply mul_ne_zero
  · rw [ne_eq, C_eq_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (by exact_mod_cast (Nat.succ_ne_zero m))
  · exact pow_ne_zero _ (X_ne_zero (0 : Fin 2))

end MathResearch.Spinor
