module
public import MathResearch.Spinor.CompatibleRow

/-! DS1: the normalized gradient is an isometric isomorphism, in every positive degree. -/
@[expose] public section
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial
namespace MathResearch.Spinor

theorem exponent_add_X (m : ℕ) (k : Fin (m + 1)) :
    exponent m k + Finsupp.single 0 1 = exponent (m + 1) k.castSucc := by
  ext i
  fin_cases i <;> simp
  omega

theorem exponent_add_Y (m : ℕ) (k : Fin (m + 1)) :
    exponent m k + Finsupp.single 1 1 = exponent (m + 1) k.succ := by
  ext i
  fin_cases i <;> simp

theorem coefficient_derivative_X (m : ℕ) (p : BinaryForm (m + 1)) (k : Fin (m + 1)) :
    coefficients m (derivative m 0 p) k =
      ((m + 1 - k.val : ℕ) : ℂ) * coefficients (m + 1) p k.castSucc := by
  change (pderiv 0 (p : MvPolynomial (Fin 2) ℂ)).coeff (exponent m k) = _
  rw [coeff_pderiv, exponent_add_X, exponent_zero]
  have hk : m - k.val + 1 = m + 1 - k.val := by omega
  rw [← Nat.cast_add_one, hk]
  exact mul_comm _ _

theorem coefficient_derivative_Y (m : ℕ) (p : BinaryForm (m + 1)) (k : Fin (m + 1)) :
    coefficients m (derivative m 1 p) k =
      ((k.val + 1 : ℕ) : ℂ) * coefficients (m + 1) p k.succ := by
  change (pderiv 1 (p : MvPolynomial (Fin 2) ℂ)).coeff (exponent m k) = _
  rw [coeff_pderiv, exponent_add_Y, exponent_one, ← Nat.cast_add_one]
  exact mul_comm _ _

private theorem square_div_of_product (a b c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : c * a = d * b) : b ^ 2 / c = a * b / d := by
  field_simp
  linear_combination -b * h

theorem derivative_weight_X (m : ℕ) (k : Fin (m + 1)) :
    ((m + 1 - k.val : ℕ) : ℝ) ^ 2 / (m.choose k : ℝ) =
      (m + 1 : ℝ) * ((m + 1 : ℝ) - k.val) / ((m + 1).choose k : ℝ) := by
  have h := Nat.choose_mul_succ_eq m k.val
  have hk : k.val ≤ m + 1 := by omega
  have hr : (m.choose k : ℝ) * (m + 1 : ℝ) =
      ((m + 1).choose k : ℝ) * ((m + 1 : ℝ) - k.val) := by
    have hc : (m.choose k : ℝ) * ((m + 1 : ℕ) : ℝ) =
        ((m + 1).choose k : ℝ) * ((m + 1 - k.val : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub hk, Nat.cast_add, Nat.cast_one] using hc
  rw [Nat.cast_sub hk, Nat.cast_add, Nat.cast_one]
  apply square_div_of_product _ _ _ _ (ne_of_gt (choose_pos m k))
    (ne_of_gt (choose_pos (m + 1) k.castSucc)) hr

theorem derivative_weight_Y (m : ℕ) (k : Fin (m + 1)) :
    ((k.val + 1 : ℕ) : ℝ) ^ 2 / (m.choose k : ℝ) =
      (m + 1 : ℝ) * (k.val + 1 : ℝ) / ((m + 1).choose (k.val + 1) : ℝ) := by
  rw [Nat.cast_add, Nat.cast_one]
  apply square_div_of_product _ _ _ _ (ne_of_gt (choose_pos m k))
    (ne_of_gt (choose_pos (m + 1) k.succ))
  have h : ((m + 1 : ℕ) : ℝ) * (m.choose k : ℝ) =
      ((m + 1).choose (k.val + 1) : ℝ) * ((k.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq m k.val
  simpa [mul_comm] using h

/-- The unnormalized gradient multiplies squared norm by n². -/
theorem derivative_norm_sq (m : ℕ) (p : BinaryForm (m + 1)) :
    ‖derivative m 0 p‖ ^ 2 + ‖derivative m 1 p‖ ^ 2 = (m + 1 : ℝ) ^ 2 * ‖p‖ ^ 2 := by
  let f : Fin (m + 2) → ℝ := fun k =>
    ‖coefficients (m + 1) p k‖ ^ 2 / ((m + 1).choose k : ℝ)
  have hx : ‖derivative m 0 p‖ ^ 2 =
      ∑ k : Fin (m + 1), (m + 1 : ℝ) * ((m + 1 : ℝ) - k.val) * f k.castSucc := by
    rw [binaryForm_norm_sq]
    apply Finset.sum_congr rfl
    intro k _
    rw [coefficient_derivative_X, norm_mul, mul_pow]
    simp only [Complex.norm_natCast]
    rw [mul_div_right_comm, derivative_weight_X]
    dsimp [f]; ring
  have hy : ‖derivative m 1 p‖ ^ 2 =
      ∑ k : Fin (m + 1), (m + 1 : ℝ) * (k.val + 1 : ℝ) * f k.succ := by
    rw [binaryForm_norm_sq]
    apply Finset.sum_congr rfl
    intro k _
    rw [coefficient_derivative_Y, norm_mul, mul_pow]
    simp only [Complex.norm_natCast]
    rw [mul_div_right_comm, derivative_weight_Y]
    dsimp [f]; ring
  have hx' : ‖derivative m 0 p‖ ^ 2 =
      ∑ k : Fin (m + 2), (m + 1 : ℝ) * ((m + 1 : ℝ) - k.val) * f k := by
    rw [Fin.sum_univ_castSucc]
    simpa using hx
  have hy' : ‖derivative m 1 p‖ ^ 2 =
      ∑ k : Fin (m + 2), (m + 1 : ℝ) * k.val * f k := by
    rw [Fin.sum_univ_succ]
    simpa using hy
  rw [hx', hy', ← Finset.sum_add_distrib, binaryForm_norm_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [f]; ring

theorem normalizedGradient_norm (m : ℕ) (p : BinaryForm (m + 1)) :
    ‖normalizedGradient m p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(normalizedGradient m p).val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 2, ‖(m + 1 : ℂ)⁻¹ • derivative m i p‖ ^ 2) = _
  simp only [Fin.sum_univ_two, norm_smul, mul_pow, ← mul_add]
  rw [derivative_norm_sq]
  have hn : (m + 1 : ℝ) ≠ 0 := by positivity
  have he : ‖(m + 1 : ℂ)⁻¹‖ ^ 2 = ((m + 1 : ℝ)⁻¹) ^ 2 := by
    congr 1
    rw [norm_inv]
    congr 1
    norm_cast
  rw [he]
  field_simp

/-- DS1's complex-linear isometric isomorphism, with n=m+1. -/
def spinorIsometry (m : ℕ) : BinaryForm (m + 1) ≃ₗᵢ[ℂ] CompatibleRow m :=
  { gradientEquiv m with norm_map' := normalizedGradient_norm m }

@[simp] theorem spinorIsometry_apply (m : ℕ) (p : BinaryForm (m + 1)) :
    spinorIsometry m p = normalizedGradient m p := rfl

@[simp] theorem spinorIsometry_symm_apply (m : ℕ) (h : CompatibleRow m) :
    (spinorIsometry m).symm h = assemble m h := rfl

instance (m : ℕ) : FiniteDimensional ℂ (CompatibleRow m) :=
  (gradientEquiv m).finiteDimensional

/-- The compatible degree-m rows have complex dimension m+2, i.e. n+1. -/
theorem finrank_compatibleRow (m : ℕ) : Module.finrank ℂ (CompatibleRow m) = m + 2 := by
  rw [← (gradientEquiv m).finrank_eq, finrank_binaryForm]

/-- DS1/v1 for every n≥1: exact gradient, exact inverse and complex dimension. -/
theorem DS1_v1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : BinaryForm n ≃ₗᵢ[ℂ] CompatibleRow (n - 1),
      (∀ (p : BinaryForm n) (i : Fin 2),
        ((e p).val i : MvPolynomial (Fin 2) ℂ) =
          (n : ℂ)⁻¹ • pderiv i (p : MvPolynomial (Fin 2) ℂ)) ∧
      (∀ h : CompatibleRow (n - 1),
        (e.symm h : MvPolynomial (Fin 2) ℂ) =
          X 0 * (h.val 0 : MvPolynomial (Fin 2) ℂ) +
          X 1 * (h.val 1 : MvPolynomial (Fin 2) ℂ)) ∧
      Module.finrank ℂ (CompatibleRow (n - 1)) = n + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_sub_one]
  refine ⟨spinorIsometry m, ?_, ?_, finrank_compatibleRow m⟩
  · intro p i
    simp [normalizedGradient, derivative]
  · intro h
    rfl

end MathResearch.Spinor
