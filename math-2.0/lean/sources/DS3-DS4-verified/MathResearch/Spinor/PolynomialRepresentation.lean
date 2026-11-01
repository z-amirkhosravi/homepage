module
public import MathResearch.Spinor.GradientIsometry
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Linear

/-! The binary polynomial representation and its genuine infinitesimal action. -/
@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace MathResearch.Spinor

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev ComplexPoly2 := MvPolynomial (Fin 2) ℂ

/-- Column j of the substitution (X,Y)M. -/
def substitution (M : Matrix2) (j : Fin 2) : ComplexPoly2 :=
  C (M 0 j) * X 0 + C (M 1 j) * X 1

/-- τ(M)p = p(M₀₀X+M₁₀Y, M₀₁X+M₁₁Y), on all polynomials. -/
def polynomialAction (M : Matrix2) : ComplexPoly2 →ₐ[ℂ] ComplexPoly2 :=
  aeval (substitution M)

@[simp] theorem polynomialAction_X (M : Matrix2) (i : Fin 2) :
    polynomialAction M (X i) = substitution M i := by simp [polynomialAction]

@[simp] theorem polynomialAction_C (M : Matrix2) (z : ℂ) :
    polynomialAction M (C z) = C z := by simp [polynomialAction]

@[simp] theorem substitution_one (i : Fin 2) : substitution 1 i = X i := by
  fin_cases i <;> simp [substitution, Matrix.one_apply]

theorem polynomialAction_one : polynomialAction 1 = AlgHom.id ℂ ComplexPoly2 := by
  ext i; simp

theorem polynomialAction_mul (M N : Matrix2) :
    polynomialAction (M * N) = (polynomialAction M).comp (polynomialAction N) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [substitution, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Polynomial chain rule in the chosen matrix convention. -/
theorem polynomialAction_chainRule (M : Matrix2) (p : ComplexPoly2) (j : Fin 2) :
    pderiv j (polynomialAction M p) =
      C (M j 0) * polynomialAction M (pderiv 0 p) +
      C (M j 1) * polynomialAction M (pderiv 1 p) := by
  induction p using MvPolynomial.induction_on generalizing j with
  | C z => simp
  | add p q hp hq => simp [hp, hq]; ring
  | mul_X p i hp =>
    fin_cases i <;> fin_cases j <;> simp [substitution, hp, pderiv_X] <;> ring

theorem substitution_homogeneous (M : Matrix2) (i : Fin 2) : (substitution M i).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · simpa using (isHomogeneous_C (Fin 2) (M 0 i)).mul (isHomogeneous_X (R := ℂ) 0)
  · simpa using (isHomogeneous_C (Fin 2) (M 1 i)).mul (isHomogeneous_X (R := ℂ) 1)

theorem polynomialAction_homogeneous (n : ℕ) (M : Matrix2) (p : BinaryForm n) :
    (polynomialAction M p).IsHomogeneous n := by
  simpa [polynomialAction] using p.property.aeval (substitution M) (substitution_homogeneous M)

/-- The complex representation on V_n, defined for the whole matrix monoid. -/
def polynomialRepresentation (n : ℕ) : Representation ℂ Matrix2 (BinaryForm n) where
  toFun M :=
    { toFun p := ⟨polynomialAction M p, polynomialAction_homogeneous n M p⟩
      map_add' _ _ := by apply Subtype.ext; simp
      map_smul' _ _ := by apply Subtype.ext; simp }
  map_one' := by ext p; simp [polynomialAction_one]
  map_mul' M N := by ext p; simp [polynomialAction_mul]

/-- Restricting the matrix-monoid action gives the usual representation of GL₂(ℂ). -/
def generalLinearPolynomialRepresentation (n : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ) (BinaryForm n) :=
  (polynomialRepresentation n).comp (Units.coeHom Matrix2)

/-- The usual first-order vector field R_M on polynomials. -/
def infinitesimal (M : Matrix2) (p : ComplexPoly2) : ComplexPoly2 :=
  substitution M 0 * pderiv 0 p + substitution M 1 * pderiv 1 p

@[simp] theorem infinitesimal_C (M : Matrix2) (z : ℂ) : infinitesimal M (C z) = 0 := by
  simp [infinitesimal]
@[simp] theorem infinitesimal_X (M : Matrix2) (i : Fin 2) : infinitesimal M (X i) = substitution M i := by
  fin_cases i <;> simp [infinitesimal, pderiv_X]
@[simp] theorem infinitesimal_add (M : Matrix2) (p q : ComplexPoly2) :
    infinitesimal M (p + q) = infinitesimal M p + infinitesimal M q := by
  simp [infinitesimal, mul_add]; ring
@[simp] theorem infinitesimal_smul (M : Matrix2) (z : ℂ) (p : ComplexPoly2) :
    infinitesimal M (z • p) = z • infinitesimal M p := by
  simp [infinitesimal, smul_add]

theorem infinitesimal_mul (M : Matrix2) (p q : ComplexPoly2) :
    infinitesimal M (p * q) = infinitesimal M p * q + p * infinitesimal M q := by
  simp [infinitesimal]; ring

/-- The infinitesimal action respects the matrix commutator. -/
theorem infinitesimal_commutator (M N : Matrix2) (p : ComplexPoly2) :
    infinitesimal M (infinitesimal N p) - infinitesimal N (infinitesimal M p) =
      infinitesimal (M * N - N * M) p := by
  simp [infinitesimal, substitution, Matrix.mul_apply, Fin.sum_univ_two, pderiv_X]
  rw [pderiv_comm (0 : Fin 2) 1 p]
  ring

theorem infinitesimal_homogeneous (m : ℕ) (M : Matrix2) (p : BinaryForm (m + 1)) :
    (infinitesimal M p).IsHomogeneous (m + 1) := by
  apply IsHomogeneous.add
  · simpa [Nat.add_comm] using (substitution_homogeneous M 0).mul (p.property.pderiv (i := 0))
  · simpa [Nat.add_comm] using (substitution_homogeneous M 1).mul (p.property.pderiv (i := 1))

/-- The infinitesimal polynomial action on positive-degree binary forms. -/
def infinitesimalAction (m : ℕ) (M : Matrix2) : BinaryForm (m + 1) →ₗ[ℂ] BinaryForm (m + 1) where
  toFun p := ⟨infinitesimal M p, infinitesimal_homogeneous m M p⟩
  map_add' _ _ := by apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; simp

theorem substitution_affine (M : Matrix2) (t : ℂ) (i : Fin 2) :
    substitution (1 + t • M) i = X i + t • substitution M i := by
  simp only [substitution, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
  fin_cases i <;> simp [Matrix.one_apply, Algebra.smul_def] <;> ring

private theorem hasDerivAt_coeff_mul (f g : ℂ → ComplexPoly2) (df dg : ComplexPoly2)
    (hf : ∀ d, HasDerivAt (fun t => (f t).coeff d) (df.coeff d) 0)
    (hg : ∀ d, HasDerivAt (fun t => (g t).coeff d) (dg.coeff d) 0) (d : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t => (f t * g t).coeff d) ((df * g 0 + f 0 * dg).coeff d) 0 := by
  convert HasDerivAt.fun_sum (u := Finset.antidiagonal d)
    (fun (x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) _ => (hf x.1).mul (hg x.2)) using 1 <;>
    simp [coeff_mul, Finset.sum_add_distrib]

/-- The coefficientwise analytic derivative of substitution at the identity. -/
theorem polynomialAction_hasDerivAt_coeff (M : Matrix2) (p : ComplexPoly2) (d : Fin 2 →₀ ℕ) :
    HasDerivAt (fun t : ℂ => (polynomialAction (1 + t • M) p).coeff d)
      ((infinitesimal M p).coeff d) 0 := by
  induction p using MvPolynomial.induction_on generalizing d with
  | C z => simpa using hasDerivAt_const (0 : ℂ) ((C z : ComplexPoly2).coeff d)
  | add p q hp hq => simpa using! (hp d).fun_add (hq d)
  | mul_X p i hp =>
    have hx (e : Fin 2 →₀ ℕ) : HasDerivAt
        (fun t : ℂ => (polynomialAction (1 + t • M) (X i)).coeff e)
        ((substitution M i).coeff e) 0 := by
      simpa [substitution_affine] using
        ((hasDerivAt_id (0 : ℂ)).mul_const ((substitution M i).coeff e)).const_add ((X i : ComplexPoly2).coeff e)
    simpa [infinitesimal_mul, polynomialAction_one] using
      hasDerivAt_coeff_mul (fun t => polynomialAction (1 + t • M) p)
        (fun t => polynomialAction (1 + t • M) (X i)) (infinitesimal M p) (substitution M i) hp hx d

/-- dτ is an actual derivative in the weighted finite-dimensional norm, not an assumed formula. -/
theorem polynomialRepresentation_hasDerivAt (m : ℕ) (M : Matrix2) (p : BinaryForm (m + 1)) :
    HasDerivAt (fun t : ℂ => polynomialRepresentation (m + 1) (1 + t • M) p)
      (infinitesimalAction m M p) 0 := by
  let e := (coefficientEquiv (m + 1)).toContinuousLinearEquiv
  have h : HasDerivAt (fun t : ℂ => e (polynomialRepresentation (m + 1) (1 + t • M) p))
      (e (infinitesimalAction m M p)) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    exact polynomialAction_hasDerivAt_coeff M p (exponent (m + 1) k)
  simpa [Function.comp_def] using e.symm.hasFDerivAt.comp_hasDerivAt 0 h

/-- The same differential along real parameters, for use with real Lie groups. -/
theorem polynomialRepresentation_hasDerivAt_real (m : ℕ) (M : Matrix2) (p : BinaryForm (m + 1)) :
    HasDerivAt (fun t : ℝ => polynomialRepresentation (m + 1) (1 + (t : ℂ) • M) p)
      (infinitesimalAction m M p) 0 := by
  simpa [Function.comp_def] using
    (polynomialRepresentation_hasDerivAt m M p).scomp (h := fun t : ℝ => (t : ℂ)) (0 : ℝ) Complex.ofRealCLM.hasDerivAt

end MathResearch.Spinor
