module
public import MathResearch.Fueter.PartialCommutation
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! Polynomial recurrence and harmonicity for the kernel numerators in EI1. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open MvPolynomial
namespace MathResearch.Fueter

abbrev RealPoly4 := MvPolynomial (Fin 4) ℝ

/-- The real norm-square polynomial in the coordinates t,x,y,z. -/
def normSqPoly : RealPoly4 := ∑ i : Fin 4, X i ^ 2

/-- The polynomial Laplacian, with all four real coordinate directions. -/
def polyLaplacian (P : RealPoly4) : RealPoly4 := ∑ i : Fin 4, pderiv i (pderiv i P)

/-- One numerator step after r derivatives. -/
def numeratorStep (r : ℕ) (j : Fin 4) (P : RealPoly4) : RealPoly4 :=
  normSqPoly * pderiv j P - C (2 * ((r : ℝ) + 2)) * (X j * P)

@[simp] theorem pderiv_normSqPoly (i : Fin 4) : pderiv i normSqPoly = 2 * X i := by
  fin_cases i <;> norm_num [normSqPoly, Fin.sum_univ_succ, pderiv_pow]

theorem normSqPoly_homogeneous : normSqPoly.IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X (R := ℝ) i).pow 2

@[simp] theorem polyLaplacian_sub (P Q : RealPoly4) :
    polyLaplacian (P - Q) = polyLaplacian P - polyLaplacian Q := by
  simp [polyLaplacian, map_sub, Finset.sum_sub_distrib]

@[simp] theorem polyLaplacian_C_mul (c : ℝ) (P : RealPoly4) :
    polyLaplacian (C c * P) = C c * polyLaplacian P := by
  simp [polyLaplacian, Finset.mul_sum]

theorem polyLaplacian_pderiv (j : Fin 4) (P : RealPoly4) :
    polyLaplacian (pderiv j P) = pderiv j (polyLaplacian P) := by
  simp only [polyLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_comm i j, pderiv_comm i j]

theorem polyLaplacian_X_mul (j : Fin 4) (P : RealPoly4) :
    polyLaplacian (X j * P) = X j * polyLaplacian P + 2 * pderiv j P := by
  have h (i : Fin 4) : pderiv i (pderiv i (X j * P)) =
      X j * pderiv i (pderiv i P) + if i = j then 2 * pderiv j P else 0 := by
    by_cases hi : i = j
    · subst i; simp; ring
    · simp [pderiv_X, hi, Ne.symm hi]
  simp only [polyLaplacian, h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem polyLaplacian_normSq_mul (P : RealPoly4) :
    polyLaplacian (normSqPoly * P) = normSqPoly * polyLaplacian P +
      4 * (∑ i : Fin 4, X i * pderiv i P) + 8 * P := by
  have h (i : Fin 4) : pderiv i (pderiv i (normSqPoly * P)) =
      normSqPoly * pderiv i (pderiv i P) + 4 * (X i * pderiv i P) + 2 * P := by
    have hc : pderiv i (2 : RealPoly4) = 0 := by
      rw [show (2 : RealPoly4) = 1 + 1 by ring, map_add, pderiv_one]
      simp
    simp [hc]; ring
  simp only [polyLaplacian, h, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem numeratorStep_homogeneous (r : ℕ) (j : Fin 4) {P : RealPoly4}
    (hP : P.IsHomogeneous (r + 1)) : (numeratorStep r j P).IsHomogeneous (r + 2) := by
  apply IsHomogeneous.sub
  · convert normSqPoly_homogeneous.mul hP.pderiv using 1; omega
  · convert (isHomogeneous_C (Fin 4) (2 * ((r : ℝ) + 2))).mul ((isHomogeneous_X (R := ℝ) j).mul hP) using 1; omega

theorem numeratorStep_laplacian (r : ℕ) (j : Fin 4) {P : RealPoly4}
    (hP : P.IsHomogeneous (r + 1)) (hH : polyLaplacian P = 0) :
    polyLaplacian (numeratorStep r j P) = 0 := by
  have he := hP.pderiv (i := j) |>.sum_X_mul_pderiv
  simp only [Nat.add_sub_cancel, nsmul_eq_mul] at he
  rw [numeratorStep, polyLaplacian_sub, polyLaplacian_normSq_mul, polyLaplacian_C_mul,
    polyLaplacian_X_mul, polyLaplacian_pderiv, hH, map_zero, he]
  simp only [mul_zero, zero_add, map_mul, map_ofNat, map_add, map_natCast]
  ring

/-- The weighted numerator steps commute in every pair of real directions. -/
theorem numeratorStep_comm (r : ℕ) (i j : Fin 4) (P : RealPoly4) :
    numeratorStep (r + 1) i (numeratorStep r j P) =
      numeratorStep (r + 1) j (numeratorStep r i P) := by
  have h2 (a : Fin 4) : pderiv a (2 : RealPoly4) = 0 := (pderiv a).map_natCast 2
  have hx : pderiv i (X j : RealPoly4) = pderiv j (X i) := by
    by_cases h : i = j
    · subst i; rfl
    · simp [pderiv_X, h, Ne.symm h]
  simp only [numeratorStep, map_sub, pderiv_mul, pderiv_normSqPoly,
    pderiv_C, h2, zero_mul, zero_add, hx, pderiv_comm i j, Nat.cast_add, Nat.cast_one,
    map_mul, map_add, map_ofNat, map_one]
  ring

/-- Component polynomials of quaternionic conjugation. -/
def conjugatePoly (k : Fin 4) : RealPoly4 := if k = 0 then X k else -X k

/-- Numerator polynomials for an arbitrary ordered list of real partial derivatives. -/
def numeratorJet : List (Fin 4) → Fin 4 → RealPoly4
  | [], k => conjugatePoly k
  | j :: l, k => numeratorStep l.length j (numeratorJet l k)

theorem conjugatePoly_homogeneous (k : Fin 4) : (conjugatePoly k).IsHomogeneous 1 := by
  unfold conjugatePoly
  split
  · exact isHomogeneous_X _ _
  · exact (isHomogeneous_X _ _).neg

theorem conjugatePoly_laplacian (k : Fin 4) : polyLaplacian (conjugatePoly k) = 0 := by
  fin_cases k <;> simp [conjugatePoly, polyLaplacian, Fin.sum_univ_succ, Pi.single_apply]

theorem numeratorJet_homogeneous (l : List (Fin 4)) (k : Fin 4) :
    (numeratorJet l k).IsHomogeneous (l.length + 1) := by
  induction l with
  | nil => exact conjugatePoly_homogeneous k
  | cons j l ih => simpa [numeratorJet, Nat.add_assoc] using numeratorStep_homogeneous l.length j ih

theorem numeratorJet_laplacian (l : List (Fin 4)) (k : Fin 4) :
    polyLaplacian (numeratorJet l k) = 0 := by
  induction l with
  | nil => exact conjugatePoly_laplacian k
  | cons j l ih => exact numeratorStep_laplacian l.length j (numeratorJet_homogeneous l k) ih

theorem numeratorJet_perm {l m : List (Fin 4)} (h : l.Perm m) (k : Fin 4) :
    numeratorJet l k = numeratorJet m k := by
  induction h with
  | nil => rfl
  | cons j h ih => simp only [numeratorJet, h.length_eq, ih]
  | swap i j l => exact numeratorStep_comm l.length j i (numeratorJet l k)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- EI1's canonical spatial multi-index numerator, with four real polynomial components. -/
def kernelNumerator (ν : Fin 3 → ℕ) (k : Fin 4) : RealPoly4 :=
  numeratorJet (spatialDerivativeList ν) k

theorem kernelNumerator_recurrence (ν : Fin 3 → ℕ) (j : Fin 3) (k : Fin 4) :
    kernelNumerator (ν + Pi.single j 1) k =
      numeratorStep (∑ i, ν i) j.succ (kernelNumerator ν k) := by
  have hp : (j.succ :: spatialDerivativeList ν).Perm
      (spatialDerivativeList (ν + Pi.single j 1)) :=
    (List.perm_append_comm.trans (spatialDerivativeList_add_single ν j))
  simpa only [kernelNumerator, numeratorJet, spatialDerivativeList_length] using
    (numeratorJet_perm hp k).symm

end MathResearch.Fueter
