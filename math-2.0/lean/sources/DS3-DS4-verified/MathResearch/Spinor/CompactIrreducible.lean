module
public import MathResearch.Spinor.CompactGroup
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Irreducibility of the compact binary-form representation, proved by its
actual Lie derivatives, distinct monomial weights, and raising/lowering maps. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Quaternion ContDiff BigOperators
open MeasureTheory MvPolynomial Filter
namespace MathResearch.Spinor

def imaginaryBasis (i : Fin 3) : ℍ := Fueter.coordinateBasis i.succ

def unitQuaternionCircle (i : Fin 3) (t : ℝ) : Fueter.UnitQuaternion := by
  refine ⟨Real.cos t • (1 : ℍ) + Real.sin t • imaginaryBasis i, ?_⟩
  have h : Quaternion.normSq (Real.cos t • (1 : ℍ) + Real.sin t • imaginaryBasis i) = 1 := by
    fin_cases i <;> simp [imaginaryBasis, Fueter.coordinateBasis_eq, Quaternion.normSq_def']
  constructor
  · rw [Quaternion.star_mul_self, h, Quaternion.coe_one]
  · rw [Quaternion.self_mul_star, h, Quaternion.coe_one]

@[simp] theorem unitQuaternionCircle_zero (i : Fin 3) : unitQuaternionCircle i 0 = 1 := by
  apply Subtype.ext
  simp [unitQuaternionCircle]

theorem unitQuaternionCircle_hasDerivAt (i : Fin 3) :
    HasDerivAt (fun t => (unitQuaternionCircle i t : ℍ)) (imaginaryBasis i) 0 := by
  simpa only [unitQuaternionCircle, Real.sin_zero, Real.cos_zero, neg_zero, zero_smul,
    one_smul, zero_add, Pi.add_apply] using!
    ((Real.hasDerivAt_cos 0).smul_const (1 : ℍ)).add
      ((Real.hasDerivAt_sin 0).smul_const (imaginaryBasis i))

def CompactPolynomialInvariant (n : ℕ) (M : Submodule ℂ (BinaryForm n)) : Prop :=
  ∀ a : Fueter.UnitQuaternion, ∀ p ∈ M,
    polynomialRepresentation n (quaternionMatrix a) p ∈ M

theorem CompactPolynomialInvariant.infinitesimal_mem {m : ℕ}
    {M : Submodule ℂ (BinaryForm (m+1))} (hM : CompactPolynomialInvariant (m+1) M)
    (p : BinaryForm (m+1)) (hp : p ∈ M) (i : Fin 3) :
    infinitesimalAction m (quaternionMatrix (imaginaryBasis i)) p ∈ M := by
  let A := fun a : ℍ => polynomialRepresentation (m+1) (quaternionMatrix a) p
  have hA : DifferentiableAt ℝ A 1 :=
    ((contDiff_quaternionPolynomialRepresentation (m+1)).comp
      (contDiff_id.prodMk (contDiff_const (c := p)))).differentiable (by simp) 1
  have ha : HasFDerivAt A (fderiv ℝ A 1) ((unitQuaternionCircle i 0 : Fueter.UnitQuaternion) : ℍ) := by
    simpa only [unitQuaternionCircle_zero, OneMemClass.coe_one] using hA.hasFDerivAt
  have hd := ha.comp_hasDerivAt 0 (unitQuaternionCircle_hasDerivAt i)
  have hh : HasDerivAt (fun t => A (unitQuaternionCircle i t))
      (infinitesimalAction m (quaternionMatrix (imaginaryBasis i)) p) 0 := by
    simpa only [unitQuaternionCircle_zero, OneMemClass.coe_one, A,
      fderiv_quaternionPolynomialRepresentation_one, Function.comp_def] using! hd
  apply (M.closed_of_finiteDimensional).mem_of_tendsto hh.tendsto_slope_zero
  filter_upwards [] with t
  exact (M.restrictScalars ℝ).smul_mem _ (M.sub_mem (hM _ p hp) (hM _ p hp))

/-- H, E and F in the usual sl₂ convention on homogeneous polynomials. -/
def polynomialWeight (m : ℕ) : Module.End ℂ (BinaryForm (m+1)) :=
  infinitesimalAction m !![1, 0; 0, -1]
def polynomialRaise (m : ℕ) : Module.End ℂ (BinaryForm (m+1)) :=
  infinitesimalAction m !![0, 1; 0, 0]
def polynomialLower (m : ℕ) : Module.End ℂ (BinaryForm (m+1)) :=
  infinitesimalAction m !![0, 0; 1, 0]

theorem polynomialWeight_val (m : ℕ) (p : BinaryForm (m+1)) :
    (polynomialWeight m p : ComplexPoly2) = X 0 * pderiv 0 p - X 1 * pderiv 1 p := by
  simp [polynomialWeight, infinitesimalAction, infinitesimal, substitution, sub_eq_add_neg]
theorem polynomialRaise_val (m : ℕ) (p : BinaryForm (m+1)) :
    (polynomialRaise m p : ComplexPoly2) = X 0 * pderiv 1 p := by
  simp [polynomialRaise, infinitesimalAction, infinitesimal, substitution]
theorem polynomialLower_val (m : ℕ) (p : BinaryForm (m+1)) :
    (polynomialLower m p : ComplexPoly2) = X 1 * pderiv 0 p := by
  simp [polynomialLower, infinitesimalAction, infinitesimal, substitution]

theorem CompactPolynomialInvariant.weight_mem {m : ℕ}
    {M : Submodule ℂ (BinaryForm (m+1))} (hM : CompactPolynomialInvariant (m+1) M)
    (p : BinaryForm (m+1)) (hp : p ∈ M) : polynomialWeight m p ∈ M := by
  have h := M.smul_mem (-Complex.I) (hM.infinitesimal_mem p hp 0)
  have he : (-Complex.I) • infinitesimalAction m (quaternionMatrix (imaginaryBasis 0)) p =
      polynomialWeight m p := by
    apply Subtype.ext
    simp [polynomialWeight, imaginaryBasis, Fueter.coordinateBasis_eq, infinitesimalAction,
      infinitesimal, substitution, quaternionMatrix, smul_eq_C_mul, ← mul_assoc, ← map_mul]
    abel
  rwa [he] at h

theorem CompactPolynomialInvariant.raise_mem {m : ℕ}
    {M : Submodule ℂ (BinaryForm (m+1))} (hM : CompactPolynomialInvariant (m+1) M)
    (p : BinaryForm (m+1)) (hp : p ∈ M) : polynomialRaise m p ∈ M := by
  have h := M.smul_mem (2⁻¹ : ℂ) (M.add_mem (hM.infinitesimal_mem p hp 1)
    (M.smul_mem (-Complex.I) (hM.infinitesimal_mem p hp 2)))
  convert h using 1
  apply Subtype.ext
  simp [imaginaryBasis, Fueter.coordinateBasis_eq, infinitesimalAction, infinitesimal,
    substitution, quaternionMatrix, polynomialRaise, smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, sub_neg_eq_add]
  ring_nf
  have hh : (2:ComplexPoly2) * C (1/2:ℂ) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : ℂ → ComplexPoly2) (show (2:ℂ)*(1/2)=1 by norm_num)
  linear_combination -(X 0 * pderiv 1 (p:ComplexPoly2)) * hh

theorem CompactPolynomialInvariant.lower_mem {m : ℕ}
    {M : Submodule ℂ (BinaryForm (m+1))} (hM : CompactPolynomialInvariant (m+1) M)
    (p : BinaryForm (m+1)) (hp : p ∈ M) : polynomialLower m p ∈ M := by
  have h := M.smul_mem (2⁻¹ : ℂ) (M.sub_mem
    (M.smul_mem (-Complex.I) (hM.infinitesimal_mem p hp 2)) (hM.infinitesimal_mem p hp 1))
  convert h using 1
  apply Subtype.ext
  simp [imaginaryBasis, Fueter.coordinateBasis_eq, infinitesimalAction, infinitesimal,
    substitution, quaternionMatrix, polynomialLower, smul_eq_C_mul]
  ring_nf
  simp only [← map_pow, Complex.I_sq, map_neg, map_one, mul_neg, mul_one, sub_neg_eq_add]
  ring_nf
  have hh : (2:ComplexPoly2) * C (1/2:ℂ) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : ℂ → ComplexPoly2) (show (2:ℂ)*(1/2)=1 by norm_num)
  linear_combination -(X 1 * pderiv 0 (p:ComplexPoly2)) * hh

theorem polynomialWeight_monomial (m : ℕ) (k : Fin (m+2)) :
    polynomialWeight m (monomialForm (m+1) k) =
      ((m+1 : ℂ) - 2*(k.val : ℂ)) • monomialForm (m+1) k := by
  apply Subtype.ext
  rw [polynomialWeight_val]
  simp only [monomialForm, X_mul_pderiv_monomial, exponent_zero, exponent_one,
    Submodule.coe_smul, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [← sub_smul]
  congr 1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem polynomialWeight_coefficients (m : ℕ) (p : BinaryForm (m+1)) (k : Fin (m+2)) :
    coefficients (m+1) (polynomialWeight m p) k =
      ((m+1 : ℂ) - 2*(k.val : ℂ)) * coefficients (m+1) p k := by
  conv_lhs => rw [← monomialForm_expansion (m+1) p]
  simp only [map_sum, map_smul, polynomialWeight_monomial, smul_smul,
    Finset.sum_apply]
  simp [coefficients, monomialForm, coeff_monomial, (exponent_injective (m+1)).eq_iff]
  ring

/-- Every weight eigenvector is a scalar multiple of a single monomial. -/
theorem polynomialWeight_eigenvector (m : ℕ) {p : BinaryForm (m+1)} (hp : p ≠ 0)
    {z : ℂ} (he : polynomialWeight m p = z • p) :
    ∃ k : Fin (m+2), coefficients (m+1) p k ≠ 0 ∧
      p = coefficients (m+1) p k • monomialForm (m+1) k := by
  have hn : ∃ k, coefficients (m+1) p k ≠ 0 := by
    by_contra h
    apply hp
    apply coefficients_injective (m+1)
    ext k
    simpa using (not_exists.mp h k)
  obtain ⟨k, hk⟩ := hn
  have hw (j : Fin (m+2)) : (((m+1:ℂ)-2*(j.val:ℂ)) - z) * coefficients (m+1) p j = 0 := by
    have h := congrArg (fun f => coefficients (m+1) f j) he
    rw [polynomialWeight_coefficients] at h
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul, sub_mul, sub_eq_zero] using h
  have hz : (m+1:ℂ)-2*(k.val:ℂ) = z := sub_eq_zero.mp ((mul_eq_zero.mp (hw k)).resolve_right hk)
  refine ⟨k, hk, ?_⟩
  apply coefficients_injective (m+1)
  ext j
  by_cases hj : k = j
  · subst j
    simp [coefficients, monomialForm]
  · have hne : (m+1:ℂ)-2*(j.val:ℂ) - z ≠ 0 := by
      rw [← hz]
      intro h
      have : (j.val:ℂ) = k.val := by linear_combination -(1/2:ℂ)*h
      exact hj (Fin.ext (Nat.cast_injective this.symm))
    have hh := (mul_eq_zero.mp (hw j)).resolve_left hne
    simp [coefficients, monomialForm, coeff_monomial, (exponent_injective (m+1)).eq_iff, hj] at *
    exact hh

theorem polynomialRaise_monomial (m : ℕ) (k : Fin (m+1)) :
    polynomialRaise m (monomialForm (m+1) k.succ) =
      ((k.val+1:ℕ):ℂ) • monomialForm (m+1) k.castSucc := by
  apply Subtype.ext
  rw [polynomialRaise_val]
  have he : Finsupp.single (0 : Fin 2) 1 + (exponent (m+1) k.succ - Finsupp.single 1 1) =
      exponent (m+1) k.castSucc := by
    ext i
    fin_cases i <;> simp [exponent]
    all_goals omega
  simp only [monomialForm, pderiv_monomial, X, monomial_mul_monomial,
    exponent_one, one_mul, he, Submodule.coe_smul, smul_monomial, smul_eq_mul, mul_one]
  rfl

theorem polynomialLower_monomial (m : ℕ) (k : Fin (m+1)) :
    polynomialLower m (monomialForm (m+1) k.castSucc) =
      ((m+1-k.val:ℕ):ℂ) • monomialForm (m+1) k.succ := by
  apply Subtype.ext
  rw [polynomialLower_val]
  have he : Finsupp.single (1 : Fin 2) 1 + (exponent (m+1) k.castSucc - Finsupp.single 0 1) =
      exponent (m+1) k.succ := by
    ext i
    fin_cases i <;> simp [exponent] <;> omega
  simp only [monomialForm, pderiv_monomial, X, monomial_mul_monomial,
    exponent_zero, one_mul, he, Submodule.coe_smul, smul_monomial, smul_eq_mul, mul_one]
  rfl

/-- Every nonzero compact-invariant subspace contains a monomial weight vector. -/
theorem CompactPolynomialInvariant.exists_monomial_mem {m : ℕ}
    {M : Submodule ℂ (BinaryForm (m+1))} (hM : CompactPolynomialInvariant (m+1) M)
    (hne : M ≠ ⊥) : ∃ k : Fin (m+2), monomialForm (m+1) k ∈ M := by
  let : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hne
  let H : Module.End ℂ M := (polynomialWeight m).restrict (fun p hp => hM.weight_mem p hp)
  obtain ⟨z, hz⟩ := H.exists_eigenvalue
  obtain ⟨p, hp⟩ := hz.exists_hasEigenvector
  have hp0 : (p : BinaryForm (m+1)) ≠ 0 := fun h => hp.2 (Subtype.ext h)
  have he : polynomialWeight m p = z • (p : BinaryForm (m+1)) :=
    congrArg Subtype.val hp.apply_eq_smul
  obtain ⟨k, hk, heq⟩ := polynomialWeight_eigenvector m hp0 he
  refine ⟨k, ?_⟩
  have hmem : coefficients (m+1) p k • monomialForm (m+1) k ∈ M := heq ▸ p.property
  simpa [smul_smul, hk] using M.smul_mem (coefficients (m+1) p k)⁻¹ hmem

/-- The elementary compact polynomial irreducibility input, with no assumed representation theorem. -/
theorem compactPolynomial_irreducible (m : ℕ) (M : Submodule ℂ (BinaryForm (m+1)))
    (hM : CompactPolynomialInvariant (m+1) M) : M = ⊥ ∨ M = ⊤ := by
  by_cases hne : M = ⊥
  · exact Or.inl hne
  right
  obtain ⟨k, hk⟩ := hM.exists_monomial_mem hne
  have hdown : ∀ k : Fin (m+2), monomialForm (m+1) k ∈ M → monomialForm (m+1) 0 ∈ M := by
    apply Fin.induction
    · exact id
    · intro j ih hj
      apply ih
      have hr := hM.raise_mem _ hj
      rw [polynomialRaise_monomial] at hr
      have hc : (((j.val+1:ℕ):ℂ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j.val)
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using M.smul_mem (((j.val+1:ℕ):ℂ))⁻¹ hr
  have hall : ∀ j : Fin (m+2), monomialForm (m+1) j ∈ M := by
    apply Fin.induction
    · exact hdown k hk
    · intro j ih
      have hl := hM.lower_mem _ ih
      rw [polynomialLower_monomial] at hl
      have hc : (((m+1-j.val:ℕ):ℂ)) ≠ 0 := by exact_mod_cast (show m+1-j.val ≠ 0 by omega)
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using M.smul_mem (((m+1-j.val:ℕ):ℂ))⁻¹ hl
  apply top_unique
  intro p _
  rw [← monomialForm_expansion (m+1) p]
  exact M.sum_mem (fun j _ => M.smul_mem _ (hall j))

end MathResearch.Spinor
