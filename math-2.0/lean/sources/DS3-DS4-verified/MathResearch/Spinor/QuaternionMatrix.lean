module
public import MathResearch.Spinor.PolynomialRepresentation
public import MathResearch.Fueter.Operators

/-! The standard quaternion embedding, with the column convention A-jB. -/
@[expose] public section
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial
namespace MathResearch.Spinor

/-- The wiki's complex matrix embedding of a real quaternion. -/
def quaternionMatrix (q : ℍ) : Matrix2 :=
  !![ (q.re : ℂ) + Complex.I * q.imI, (q.imJ : ℂ) + Complex.I * q.imK;
      -(q.imJ : ℂ) + Complex.I * q.imK, (q.re : ℂ) - Complex.I * q.imI ]

@[simp] theorem quaternionMatrix_add (q r : ℍ) :
    quaternionMatrix (q + r) = quaternionMatrix q + quaternionMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix] <;> ring

@[simp] theorem quaternionMatrix_one : quaternionMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix]

@[simp] theorem quaternionMatrix_mul (q r : ℍ) :
    quaternionMatrix (q * r) = quaternionMatrix q * quaternionMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [quaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem quaternionMatrix_real (r : ℝ) :
    quaternionMatrix (r : ℍ) = algebraMap ℝ Matrix2 r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix, algebraMap, Algebra.algebraMap]

/-- A real algebra embedding; its multiplication order is ordinary matrix multiplication. -/
def quaternionMatrixHom : ℍ →ₐ[ℝ] Matrix2 where
  toFun := quaternionMatrix
  map_one' := quaternionMatrix_one
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [quaternionMatrix]
  map_add' := quaternionMatrix_add
  map_mul' := quaternionMatrix_mul
  commutes' := quaternionMatrix_real

theorem quaternionMatrix_injective : Function.Injective quaternionMatrix := by
  intro q r h
  have h00 := congrArg (fun M : Matrix2 => M 0 0) h
  have h01 := congrArg (fun M : Matrix2 => M 0 1) h
  ext
  · simpa [quaternionMatrix] using congrArg Complex.re h00
  · simpa [quaternionMatrix] using congrArg Complex.im h00
  · simpa [quaternionMatrix] using congrArg Complex.re h01
  · simpa [quaternionMatrix] using congrArg Complex.im h01

/-- Left quaternion multiplication acts on the column representing A-jB. -/
theorem quaternionMatrix_pack (q : ℍ) (a b : ℂ) :
    pack (quaternionMatrix q 0 0 * a + quaternionMatrix q 0 1 * b)
      (quaternionMatrix q 1 0 * a + quaternionMatrix q 1 1 * b) = q * pack a b := by
  ext <;> simp [pack_components, quaternionMatrix] <;> ring

theorem quaternionMatrix_real_smul (r : ℝ) (q : ℍ) :
    quaternionMatrix (r • q) = (r : ℂ) • quaternionMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix] <;> ring

/-- Restriction of the matrix representation along the quaternion algebra embedding. -/
def quaternionPolynomialRepresentation (n : ℕ) : Representation ℂ ℍ (BinaryForm n) :=
  (polynomialRepresentation n).comp quaternionMatrixHom.toMonoidHom

/-- The infinitesimal quaternion action is the real derivative along 1+t v. -/
theorem quaternionPolynomialRepresentation_hasDerivAt (m : ℕ) (v : ℍ) (p : BinaryForm (m + 1)) :
    HasDerivAt (fun t : ℝ => quaternionPolynomialRepresentation (m + 1) (1 + t • v) p)
      (infinitesimalAction m (quaternionMatrix v) p) 0 := by
  change HasDerivAt (fun t : ℝ => polynomialRepresentation (m + 1) (quaternionMatrix (1 + t • v)) p)
    (infinitesimalAction m (quaternionMatrix v) p) 0
  simpa only [quaternionMatrix_add, quaternionMatrix_one, quaternionMatrix_real_smul] using
    polynomialRepresentation_hasDerivAt_real m (quaternionMatrix v) p

/-- The action on the unit quaternion group; no unitarity claim is built into this definition. -/
def unitQuaternionPolynomialRepresentation (n : ℕ) : Representation ℂ (unitary ℍ) (BinaryForm n) :=
  (quaternionPolynomialRepresentation n).comp (unitary ℍ).subtype

/-- The i,j,k generators have precisely the signs of L8. -/
theorem infinitesimal_i (p : ComplexPoly2) :
    infinitesimal (quaternionMatrix (⟨0, 1, 0, 0⟩ : ℍ)) p =
      C Complex.I * (X 0 * pderiv 0 p - X 1 * pderiv 1 p) := by
  simp [infinitesimal, substitution, quaternionMatrix]; ring

theorem infinitesimal_j (p : ComplexPoly2) :
    infinitesimal (quaternionMatrix quaternionJ) p = -X 1 * pderiv 0 p + X 0 * pderiv 1 p := by
  simp [infinitesimal, substitution, quaternionMatrix, quaternionJ]

theorem infinitesimal_k (p : ComplexPoly2) :
    infinitesimal (quaternionMatrix (⟨0, 0, 0, 1⟩ : ℍ)) p =
      C Complex.I * (X 1 * pderiv 0 p + X 0 * pderiv 1 p) := by
  simp [infinitesimal, substitution, quaternionMatrix]; ring

/-- The infinitesimal real scalar action is n r times the identity. -/
theorem infinitesimal_real (n : ℕ) (r : ℝ) (p : BinaryForm n) :
    infinitesimal (quaternionMatrix (r : ℍ)) p = ((n : ℂ) * r) • (p : ComplexPoly2) := by
  have he := p.property.sum_X_mul_pderiv
  simp only [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ] at he
  calc
    _ = C (r : ℂ) * (X 0 * pderiv 0 (p : ComplexPoly2) + X 1 * pderiv 1 (p : ComplexPoly2)) := by
      simp [infinitesimal, substitution, quaternionMatrix]; ring
    _ = _ := by rw [he]; simp [smul_eq_C_mul]; ring

/-- C_v = (conj(v)q-conj(q)v)/2, defined for every q and v. -/
def connectionCoefficient (q v : ℍ) : ℍ := (2 : ℝ)⁻¹ • (star v * q - star q * v)

/-- Removing the real part is exactly the antisymmetric half-difference C_v. -/
theorem connectionCoefficient_eq (q v : ℍ) :
    connectionCoefficient q v = star v * q - ((star v * q).re : ℍ) := by
  ext <;> simp [connectionCoefficient] <;> ring

/-- Unnormalized T_n, kept separate from DS1's isometric normalization. -/
def gradientRow (m : ℕ) (p : BinaryForm (m + 1)) : FormRow m :=
  WithLp.toLp 2 (fun i => derivative m i p)

/-- Coefficients of the quaternion-valued polynomial p_X-jp_Y, at every exponent. -/
def polynomialFueterCoefficients (p : ComplexPoly2) (d : Fin 2 →₀ ℕ) : ℍ :=
  pack ((pderiv 0 p).coeff d) ((pderiv 1 p).coeff d)

/-- Quaternion coefficients of the actual unnormalized p_X-jp_Y. -/
def fueterCoefficients (m : ℕ) (p : BinaryForm (m + 1)) : Fin (m + 1) → ℍ :=
  quaternionCoefficients m (gradientRow m p)

theorem fueterCoefficients_eq (m : ℕ) (p : BinaryForm (m + 1)) (k : Fin (m + 1)) :
    fueterCoefficients m p k = polynomialFueterCoefficients p (exponent m k) := rfl

end MathResearch.Spinor
