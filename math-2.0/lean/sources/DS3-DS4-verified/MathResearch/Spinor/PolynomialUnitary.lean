module
public import MathResearch.Spinor.CurvatureWitness

/-! Exact norm scaling of the polynomial representation, in every degree. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
open MvPolynomial
namespace MathResearch.Spinor

theorem derivative_action (m : ℕ) (M : Matrix2) (p : BinaryForm (m+1)) (j : Fin 2) :
    derivative m j (polynomialRepresentation (m+1) M p) =
      M j 0 • polynomialRepresentation m M (derivative m 0 p) +
      M j 1 • polynomialRepresentation m M (derivative m 1 p) := by
  apply Subtype.ext
  change pderiv j (polynomialAction M p) = M j 0 • polynomialAction M (pderiv 0 p) + M j 1 • polynomialAction M (pderiv 1 p)
  simpa only [smul_eq_C_mul] using polynomialAction_chainRule M p j

/-- A quaternion matrix scales the squared column norm by its quaternion norm squared. -/
theorem quaternionMatrix_column_norm (a : ℍ) (z w : ℂ) :
    ‖quaternionMatrix a 0 0*z+quaternionMatrix a 0 1*w‖^2 +
    ‖quaternionMatrix a 1 0*z+quaternionMatrix a 1 1*w‖^2 =
      ‖a‖^2*(‖z‖^2+‖w‖^2) := by
  have h := congrArg (fun q : ℍ => ‖q‖^2) (quaternionMatrix_pack a z w)
  simpa [pack_norm_sq, norm_mul, mul_pow] using h

theorem quaternionMatrix_form_pair_norm (m : ℕ) (a : ℍ) (p q : BinaryForm m) :
    ‖quaternionMatrix a 0 0 • p+quaternionMatrix a 0 1 • q‖^2 +
    ‖quaternionMatrix a 1 0 • p+quaternionMatrix a 1 1 • q‖^2 =
      ‖a‖^2*(‖p‖^2+‖q‖^2) := by
  simp only [binaryForm_norm_sq, map_add, map_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ← Finset.sum_add_distrib, ← add_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [quaternionMatrix_column_norm]
  ring

/-- The actual binomially weighted norm scales by |a|^n under τ_n(a). -/
theorem quaternionAction_norm (n : ℕ) (a : ℍ) (p : BinaryForm n) :
    ‖polynomialRepresentation n (quaternionMatrix a) p‖ = ‖a‖^n*‖p‖ := by
  induction n with
  | zero =>
    have he : polynomialRepresentation 0 (quaternionMatrix a) p = p := by
      have hp := monomialForm_expansion 0 p
      change (∑ k : Fin 1, coefficients 0 p k • monomialForm 0 k) = p at hp
      rw [Fin.sum_univ_one] at hp
      rw [← hp, map_smul]
      congr 1
      apply Subtype.ext
      simp [polynomialRepresentation, monomialForm, exponent, polynomialAction]
    simp [he]
  | succ m ih =>
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))).mp
    have hn : (m+1:ℝ)^2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hn
    rw [← derivative_norm_sq, derivative_action, derivative_action, quaternionMatrix_form_pair_norm,
      ih, ih, mul_pow, mul_pow, ← mul_add, derivative_norm_sq]
    simp only [pow_succ, mul_pow]
    ring

theorem unitQuaternionAction_norm (n : ℕ) (a : ℍ) (ha : Quaternion.normSq a=1) (p : BinaryForm n) :
    ‖polynomialRepresentation n (quaternionMatrix a) p‖ = ‖p‖ := by
  rw [quaternionAction_norm]
  have hn : ‖a‖=1 := by
    have := Quaternion.normSq_eq_norm_mul_self a
    nlinarith [norm_nonneg a]
  simp [hn]

end MathResearch.Spinor
