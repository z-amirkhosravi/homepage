module
public import MathResearch.Spinor.WeightedMeasure

/-! The coefficient matrix and transpose in DS2's row action C3, with right complex scalars. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators
namespace MathResearch.Spinor

/-- Columns are the coefficients of τ_m(M) on the ordered monomial basis. -/
def coefficientActionMatrix (m : ℕ) (M : Matrix2) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  fun k l => coefficients m (polynomialRepresentation m M (monomialForm m l)) k

theorem coefficients_action (m : ℕ) (M : Matrix2) (p : BinaryForm m) (k : Fin (m+1)) :
    coefficients m (polynomialRepresentation m M p) k =
      ∑ l, coefficientActionMatrix m M k l * coefficients m p l := by
  conv_lhs => rw [← monomialForm_expansion m p]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

/-- On a row, this is right multiplication by the transpose of the coefficient matrix.
The complex entries multiply quaternion coefficients on the right. -/
def rowSubstitution (m : ℕ) (M : Matrix2) (h : Fin (m+1) → ℍ) (k : Fin (m+1)) : ℍ :=
  ∑ l, h l * ((coefficientActionMatrix m M).transpose l k : ℍ)

theorem fueterCoefficients_action (m : ℕ) (a : ℍ) (p : BinaryForm (m+1)) (k : Fin (m+1)) :
    fueterCoefficients m (polynomialRepresentation (m+1) (quaternionMatrix a) p) k =
      a * rowSubstitution m (quaternionMatrix a) (fueterCoefficients m p) k := by
  change pack (coefficients m (derivative m 0 (polynomialRepresentation (m+1) (quaternionMatrix a) p)) k)
    (coefficients m (derivative m 1 (polynomialRepresentation (m+1) (quaternionMatrix a) p)) k) = _
  rw [derivative_action, derivative_action]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [quaternionMatrix_pack, coefficients_action, coefficients_action, pack_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact pack_smul _ _ _

theorem fueterCoefficients_real_smul (m : ℕ) (r : ℝ) (p : BinaryForm (m+1)) (k : Fin (m+1)) :
    fueterCoefficients m (r • p) k = r • fueterCoefficients m p k := by
  change pack (coefficients m (derivative m 0 ((r:ℂ) • p)) k)
    (coefficients m (derivative m 1 ((r:ℂ) • p)) k) = _
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact pack_real_smul _ _ _

/-- The actual normalized quaternion coefficient row T_n/n, n=m+1. -/
def normalizedFueterRow (m : ℕ) (p : BinaryForm (m+1)) (k : Fin (m+1)) : ℍ :=
  (m+1:ℝ)⁻¹ • fueterCoefficients m p k

/-- C3, before inserting the inverse group element. -/
def rowBallAction (m : ℕ) (a : QuaternionMatrix2) (h : ℍ → Fin (m+1) → ℍ)
    (q : ℍ) (k : Fin (m+1)) : ℍ :=
  (Quaternion.normSq (mobiusDenominator a q))⁻¹ •
    ((mobiusDenominator a q)⁻¹ *
      rowSubstitution m (quaternionMatrix ((mobiusDenominator a q)⁻¹)) (h (mobiusPoint a q)) k)

/-- C3 with the same inverse-element convention as C7. -/
def rowBallRepresentation (m : ℕ) (g : QuaternionMatrix2) := rowBallAction m (signatureAdjoint g)

/-- The exact normalized C3/C7 intertwiner, including transpose and both multiplication sides. -/
theorem DS2_row_intertwining (m : ℕ) (g : QuaternionMatrix2) (f : ℍ → BinaryForm (m+1))
    (q : ℍ) (k : Fin (m+1)) :
    normalizedFueterRow m (ballRepresentation (m+1) g f q) k =
      rowBallRepresentation m g (fun x => normalizedFueterRow m (f x)) q k := by
  simp only [ballRepresentation, ballAction, normalizedFueterRow, rowBallRepresentation, rowBallAction,
    fueterCoefficients_real_smul, fueterCoefficients_action, rowSubstitution,
    smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm]
  exact smul_comm _ _ _

end MathResearch.Spinor
