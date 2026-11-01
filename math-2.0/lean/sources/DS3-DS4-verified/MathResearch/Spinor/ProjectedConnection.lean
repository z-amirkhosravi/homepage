module
public import MathResearch.Spinor.QuaternionMatrix

/-! All-degree projected connection identities, SC2/v1. -/
@[expose] public section
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial
namespace MathResearch.Spinor

/-- Left multiplication of a two-component polynomial column by a complex matrix. -/
def matrixColumn (M : Matrix2) (h : Fin 2 → ComplexPoly2) (i : Fin 2) : ComplexPoly2 :=
  C (M i 0) * h 0 + C (M i 1) * h 1

/-- Euler operator X∂X+Y∂Y on arbitrary binary polynomials. -/
def euler (p : ComplexPoly2) : ComplexPoly2 := X 0 * pderiv 0 p + X 1 * pderiv 1 p

/-- The unweighted operator identity L10, before homogeneity is imposed. -/
theorem projected_full_identity (q : ℍ) (p : ComplexPoly2) (i : Fin 2) :
    (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun j => pderiv j (infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p)) i) =
    2 * matrixColumn (quaternionMatrix q) (fun j => euler (pderiv j p) + 2 * pderiv j p) i := by
  have hI : (C Complex.I : ComplexPoly2) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  fin_cases i <;>
    simp [matrixColumn, infinitesimal, substitution, quaternionMatrix, Fueter.coordinateBasis_eq,
      Fin.sum_univ_succ, euler, pderiv_X] <;>
    ring_nf <;> simp [hI] <;> ring

/-- The projected compact contribution, still for arbitrary polynomials. -/
theorem projected_connection_identity (q : ℍ) (p : ComplexPoly2) (i : Fin 2) :
    (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun j => pderiv j (infinitesimal (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p)) i) =
    matrixColumn (quaternionMatrix q) (fun j => euler (pderiv j p) + 3 * pderiv j p) i := by
  have hI : (C Complex.I : ComplexPoly2) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  have hcomm := pderiv_comm (0 : Fin 2) 1 p
  fin_cases i <;>
    simp [matrixColumn, infinitesimal, substitution, quaternionMatrix, connectionCoefficient_eq,
      Fueter.coordinateBasis_eq, Fin.sum_univ_succ, euler, pderiv_X] <;>
    simp only [hcomm] <;>
    ring_nf <;> simp [hI] <;> ring

theorem euler_homogeneous (m : ℕ) (p : BinaryForm m) :
    euler p = (m : ℂ) • (p : ComplexPoly2) := by
  simpa [euler, Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ] using p.property.sum_X_mul_pderiv

/-- The first SC2 identity in polynomial column coordinates. -/
theorem projected_full_homogeneous (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) (i : Fin 2) :
    (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun j => pderiv j (infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p)) i) =
    (2 * (m + 2) : ℂ) • matrixColumn (quaternionMatrix q) (fun j => pderiv j (p : ComplexPoly2)) i := by
  rw [projected_full_identity]
  have he (j : Fin 2) : euler (pderiv j (p : ComplexPoly2)) = (m : ℂ) • pderiv j (p : ComplexPoly2) :=
    euler_homogeneous m (derivative m j p)
  simp [matrixColumn, he, smul_eq_C_mul, map_ofNat]
  ring

/-- The real scalar removed from conjugate(v)q is the Euclidean inner product. -/
theorem connectionCoefficient_eq_inner (q v : ℍ) :
    connectionCoefficient q v = star v * q - (inner ℝ v q : ℍ) := by
  rw [connectionCoefficient_eq]
  congr 2
  simp [Quaternion.inner_def]

/-- Reconstruction in the real orthonormal basis 1,i,j,k. -/
theorem coordinateBasis_inner_sum (q : ℍ) :
    (∑ μ : Fin 4, (inner ℝ (Fueter.coordinateBasis μ) q) • Fueter.coordinateBasis μ) = q := by
  ext <;> simp [Fueter.coordinateBasis_eq, Fin.sum_univ_succ, Quaternion.inner_def]

theorem infinitesimal_quaternion_sub (a b : ℍ) (p : ComplexPoly2) :
    infinitesimal (quaternionMatrix (a - b)) p =
      infinitesimal (quaternionMatrix a) p - infinitesimal (quaternionMatrix b) p := by
  have h := quaternionMatrixHom.map_sub a b
  change quaternionMatrix (a - b) = quaternionMatrix a - quaternionMatrix b at h
  rw [h]
  simp [infinitesimal, substitution, sub_mul]
  ring

/-- The scalar correction in L11, reconstructed before using homogeneity. -/
theorem matrixColumn_inner_sum (q : ℍ) (h : Fin 2 → ComplexPoly2) (i : Fin 2) :
    (∑ μ : Fin 4, (inner ℝ (Fueter.coordinateBasis μ) q : ℂ) •
      matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ)) h i) =
      matrixColumn (quaternionMatrix q) h i := by
  have hs : (∑ μ : Fin 4, (inner ℝ (Fueter.coordinateBasis μ) q : ℂ) •
      quaternionMatrix (Fueter.coordinateBasis μ)) = quaternionMatrix q := by
    calc
      _ = ∑ μ : Fin 4, quaternionMatrix ((inner ℝ (Fueter.coordinateBasis μ) q) •
          Fueter.coordinateBasis μ) := by simp only [quaternionMatrix_real_smul]
      _ = quaternionMatrixHom (∑ μ : Fin 4, (inner ℝ (Fueter.coordinateBasis μ) q) •
          Fueter.coordinateBasis μ) := (map_sum quaternionMatrixHom _ _).symm
      _ = _ := congrArg quaternionMatrix (coordinateBasis_inner_sum q)
  have hi := congrArg (fun M => matrixColumn M h i) hs
  simpa [matrixColumn, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_C_mul, Finset.sum_add_distrib, Finset.sum_mul,
    map_sum, map_mul, mul_assoc, mul_add] using hi

/-- The second SC2 identity: L9 minus the degree-n scalar action, as in L11. -/
theorem projected_connection_homogeneous (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) (i : Fin 2) :
    (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
      (fun j => pderiv j (infinitesimal (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p)) i) =
    (m + 3 : ℂ) • matrixColumn (quaternionMatrix q) (fun j => pderiv j (p : ComplexPoly2)) i := by
  have hsplit (v : ℍ) :
      infinitesimal (quaternionMatrix (connectionCoefficient q v)) p =
        infinitesimal (quaternionMatrix (star v * q)) p -
        ((m + 1 : ℂ) * (inner ℝ v q : ℂ)) • (p : ComplexPoly2) := by
    rw [connectionCoefficient_eq_inner, infinitesimal_quaternion_sub, infinitesimal_real]
    simp
  calc
    _ = (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
          (fun j => pderiv j (infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p)) i) -
        (m + 1 : ℂ) • (∑ μ : Fin 4, (inner ℝ (Fueter.coordinateBasis μ) q : ℂ) •
          matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ)) (fun j => pderiv j (p : ComplexPoly2)) i) := by
      simp only [hsplit, map_sub, Finset.smul_sum, smul_smul,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro μ _
      simp [matrixColumn, smul_eq_C_mul]
      ring
    _ = _ := by
      rw [projected_full_homogeneous, matrixColumn_inner_sum, ← sub_smul]
      congr 1
      ring

/-- Taking a coefficient commutes with the matrix action, using left quaternion multiplication. -/
theorem matrixColumn_pack_coeff (q : ℍ) (h : Fin 2 → ComplexPoly2) (d : Fin 2 →₀ ℕ) :
    pack ((matrixColumn (quaternionMatrix q) h 0).coeff d)
      ((matrixColumn (quaternionMatrix q) h 1).coeff d) = q * pack ((h 0).coeff d) ((h 1).coeff d) := by
  simpa [matrixColumn] using quaternionMatrix_pack q ((h 0).coeff d) ((h 1).coeff d)

theorem pack_sum {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    pack (∑ i ∈ s, a i) (∑ i ∈ s, b i) = ∑ i ∈ s, pack (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pack]
  | @insert i s hi ih => simp [hi, pack_add, ih]

theorem pack_real_smul (r : ℝ) (a b : ℂ) :
    pack ((r : ℂ) * a) ((r : ℂ) * b) = r • pack a b := by
  ext <;> simp [pack_components]

/-- Translate any scalar polynomial-column identity into the exact quaternion coefficient identity. -/
theorem column_identity_to_quaternion (q : ℍ) (P : Fin 4 → ComplexPoly2)
    (p : ComplexPoly2) (r : ℝ)
    (h : ∀ i : Fin 2, (∑ μ : Fin 4, matrixColumn (quaternionMatrix (Fueter.coordinateBasis μ))
        (fun j => pderiv j (P μ)) i) =
      (r : ℂ) • matrixColumn (quaternionMatrix q) (fun j => pderiv j p) i)
    (d : Fin 2 →₀ ℕ) :
    (∑ μ : Fin 4, Fueter.coordinateBasis μ *
      pack ((pderiv 0 (P μ)).coeff d) ((pderiv 1 (P μ)).coeff d)) =
    r • (q * pack ((pderiv 0 p).coeff d) ((pderiv 1 p).coeff d)) := by
  have hh := congrArg₂ pack (congrArg (fun f : ComplexPoly2 => f.coeff d) (h 0))
    (congrArg (fun f : ComplexPoly2 => f.coeff d) (h 1))
  simpa [pack_sum, matrixColumn_pack_coeff, pack_real_smul] using hh

/-- First SC2 formula, as equality of the complete quaternion coefficient rows. -/
theorem projected_full_quaternion (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) :
    (fun k => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      fueterCoefficients m (infinitesimalAction m (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p) k) =
    (fun k => (2 * (m + 2) : ℝ) • (q * fueterCoefficients m p k)) := by
  funext k
  apply column_identity_to_quaternion q
    (fun μ => infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p) p
    (2 * (m + 2)) _ (exponent m k)
  intro i
  simpa using projected_full_homogeneous m q p i

/-- Second SC2 formula, as equality of the complete quaternion coefficient rows. -/
theorem projected_connection_quaternion (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) :
    (fun k => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      fueterCoefficients m (infinitesimalAction m (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p) k) =
    (fun k => (m + 3 : ℝ) • (q * fueterCoefficients m p k)) := by
  funext k
  apply column_identity_to_quaternion q
    (fun μ => infinitesimal (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p) p
    (m + 3) _ (exponent m k)
  intro i
  simpa using projected_connection_homogeneous m q p i

/-- SC2/v1, with m=n-1: both identities, for every quaternion q and every degree n≥1. -/
theorem SC2_v1_coefficients (m : ℕ) (q : ℍ) (p : BinaryForm (m + 1)) :
    ((fun k => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      fueterCoefficients m (infinitesimalAction m (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p) k) =
      (fun k => (2 * (m + 2) : ℝ) • (q * fueterCoefficients m p k))) ∧
    ((fun k => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      fueterCoefficients m (infinitesimalAction m (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p) k) =
      (fun k => (m + 3 : ℝ) • (q * fueterCoefficients m p k))) :=
  ⟨projected_full_quaternion m q p, projected_connection_quaternion m q p⟩

/-- SC2/v1 with the wiki's n: both quaternion polynomial identities, coefficientwise at every exponent. -/
theorem SC2_v1 (n : ℕ) (hn : 1 ≤ n) (q : ℍ) (p : BinaryForm n) :
    ((fun d => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      polynomialFueterCoefficients (infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p) d) =
      (fun d => (2 * (n + 1) : ℝ) • (q * polynomialFueterCoefficients p d))) ∧
    ((fun d => ∑ μ : Fin 4, Fueter.coordinateBasis μ *
      polynomialFueterCoefficients (infinitesimal (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p) d) =
      (fun d => (n + 2 : ℝ) • (q * polynomialFueterCoefficients p d))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  constructor
  · funext d
    apply column_identity_to_quaternion q
      (fun μ => infinitesimal (quaternionMatrix (star (Fueter.coordinateBasis μ) * q)) p) p
      (2 * (m.succ + 1)) _ d
    intro i
    convert projected_full_homogeneous m q p i using 1; norm_num [Nat.cast_succ, add_assoc]
  · funext d
    apply column_identity_to_quaternion q
      (fun μ => infinitesimal (quaternionMatrix (connectionCoefficient q (Fueter.coordinateBasis μ))) p) p
      (m.succ + 2) _ d
    intro i
    convert projected_connection_homogeneous m q p i using 1; norm_num [Nat.cast_succ, add_assoc]

end MathResearch.Spinor
