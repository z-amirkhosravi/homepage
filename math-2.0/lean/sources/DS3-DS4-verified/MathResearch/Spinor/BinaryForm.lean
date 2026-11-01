module
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Quaternion

/-! Binary homogeneous polynomials with the binomially weighted Hermitian norm. -/
@[expose] public section
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial
namespace MathResearch.Spinor

/-- The actual mathlib subspace of degree-n homogeneous polynomials in X and Y. -/
abbrev BinaryForm (n : ℕ) := homogeneousSubmodule (Fin 2) ℂ n

/-- Exponent of X^(n-k) Y^k. -/
def exponent (n : ℕ) (k : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) (n - k.val) + Finsupp.single 1 k.val

@[simp] theorem exponent_zero (n : ℕ) (k : Fin (n + 1)) : exponent n k 0 = n - k := by
  simp [exponent]
@[simp] theorem exponent_one (n : ℕ) (k : Fin (n + 1)) : exponent n k 1 = k := by
  simp [exponent]

@[simp] theorem exponent_degree (n : ℕ) (k : Fin (n + 1)) : (exponent n k).degree = n := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_succ]; omega

theorem exponent_injective (n : ℕ) : Function.Injective (exponent n) := by
  intro k l h
  have := congrArg (fun d => d 1) h
  exact Fin.ext (by simpa using this)

theorem exponent_of_degree (n : ℕ) (d : Fin 2 →₀ ℕ) (hd : d.degree = n) :
    ∃ k : Fin (n + 1), exponent n k = d := by
  have h : d 0 + d 1 = n := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ] using hd
  refine ⟨⟨d 1, by omega⟩, ?_⟩
  ext i; fin_cases i <;> simp
  omega

/-- The ordinary monomial coefficients, without binomial normalization. -/
def coefficients (n : ℕ) : BinaryForm n →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun p k := (p : MvPolynomial (Fin 2) ℂ).coeff (exponent n k)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem coefficients_injective (n : ℕ) : Function.Injective (coefficients n) := by
  intro p q h
  apply Subtype.ext
  ext d
  by_cases hd : d.degree = n
  · obtain ⟨k, rfl⟩ := exponent_of_degree n d hd
    exact congrFun h k
  · have hp : (p : MvPolynomial (Fin 2) ℂ).coeff d = 0 := by
      by_contra hc
      exact hd (by simpa [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Pi.one_apply] using p.property hc)
    have hq : (q : MvPolynomial (Fin 2) ℂ).coeff d = 0 := by
      by_contra hc
      exact hd (by simpa [Finsupp.degree_eq_sum, Finsupp.weight_eq_sum, Pi.one_apply] using q.property hc)
    rw [hp, hq]

theorem coefficients_surjective (n : ℕ) : Function.Surjective (coefficients n) := by
  intro c
  let p : BinaryForm n := ⟨∑ k, monomial (exponent n k) (c k), by
    apply IsHomogeneous.sum
    intro k _
    exact isHomogeneous_monomial (c k) (exponent_degree n k)⟩
  refine ⟨p, ?_⟩
  ext k
  simp [coefficients, p, coeff_monomial, (exponent_injective n).eq_iff]

/-- All n+1 coefficients freely parametrize the homogeneous polynomial submodule. -/
def coefficientEquiv (n : ℕ) : BinaryForm n ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearEquiv.ofBijective (coefficients n) ⟨coefficients_injective n, coefficients_surjective n⟩

instance (n : ℕ) : FiniteDimensional ℂ (BinaryForm n) :=
  (coefficientEquiv n).symm.finiteDimensional

@[simp] theorem finrank_binaryForm (n : ℕ) : Module.finrank ℂ (BinaryForm n) = n + 1 := by
  rw [(coefficientEquiv n).finrank_eq]; simp

/-- The coefficient embedding defining the norm: c_k / sqrt(binomial(n,k)). -/
def weightedCoefficients (n : ℕ) : BinaryForm n →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)) where
  toFun p := WithLp.toLp 2 (fun k => coefficients n p k / (Real.sqrt (n.choose k) : ℂ))
  map_add' _ _ := by ext; simp [add_div]
  map_smul' _ _ := by ext; simp [mul_div_assoc]

theorem choose_pos (n : ℕ) (k : Fin (n + 1)) : (0 : ℝ) < n.choose k := by
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ k.isLt)

theorem weightedCoefficients_injective (n : ℕ) : Function.Injective (weightedCoefficients n) := by
  intro p q h
  apply coefficients_injective n
  ext k
  have hk : (Real.sqrt (n.choose k) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (choose_pos n k)).ne'
  exact (div_left_inj' hk).mp (congrArg (fun x => x k) h)

instance (n : ℕ) : NormedAddCommGroup (BinaryForm n) :=
  NormedAddCommGroup.induced _ _ (weightedCoefficients n) (weightedCoefficients_injective n)
instance (n : ℕ) : NormedSpace ℂ (BinaryForm n) :=
  NormedSpace.induced _ _ _ (weightedCoefficients n)
instance (n : ℕ) : InnerProductSpace ℂ (BinaryForm n) :=
  InnerProductSpace.induced (weightedCoefficients n)

/-- The norm is independently specified by the wiki's binomial weights. -/
theorem binaryForm_norm_sq (n : ℕ) (p : BinaryForm n) :
    ‖p‖ ^ 2 = ∑ k, ‖coefficients n p k‖ ^ 2 / (n.choose k : ℝ) := by
  change ‖weightedCoefficients n p‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro k _
  simp [weightedCoefficients, div_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt (choose_pos n k))]

end MathResearch.Spinor
