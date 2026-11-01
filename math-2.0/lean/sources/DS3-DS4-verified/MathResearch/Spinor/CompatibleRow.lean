module
public import MathResearch.Spinor.BinaryForm

/-! The compatible rows A-jB, with the norm and right complex action made explicit. -/
@[expose] public section
noncomputable section
open scoped BigOperators Quaternion
open MvPolynomial
namespace MathResearch.Spinor

/-- Two homogeneous complex polynomials, with the sum-of-squares norm. -/
abbrev FormRow (m : ℕ) := PiLp 2 (fun _ : Fin 2 => BinaryForm m)

/-- Compatibility is the actual equality of mathlib polynomial partial derivatives. -/
def compatibleRows (m : ℕ) : Submodule ℂ (FormRow m) where
  carrier := {h | pderiv 1 (h 0 : MvPolynomial (Fin 2) ℂ) = pderiv 0 (h 1 : MvPolynomial (Fin 2) ℂ)}
  zero_mem' := by simp
  add_mem' ha hb := by
    dsimp at ha hb ⊢
    simp only [map_add, ha, hb]
  smul_mem' c h hh := by
    dsimp at hh ⊢
    simp only [Derivation.map_smul, hh]

abbrev CompatibleRow (m : ℕ) := compatibleRows m

/-- Quaternion j, in mathlib's standard real coordinates. -/
def quaternionJ : ℍ := ⟨0, 0, 1, 0⟩

/-- The column convention (A,B) ↦ A-jB; scalars on the quaternion side act on the right. -/
def pack (a b : ℂ) : ℍ := (a : ℍ) - quaternionJ * (b : ℍ)

theorem pack_components (a b : ℂ) : pack a b = ⟨a.re, a.im, -b.re, b.im⟩ := by
  ext <;> simp [pack, quaternionJ]

theorem pack_injective : Function.Injective (fun x : ℂ × ℂ => pack x.1 x.2) := by
  intro x y h
  simp only [pack_components] at h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  exact Prod.ext (Complex.ext h0 h1) (Complex.ext (neg_injective h2) h3)

theorem pack_surjective : Function.Surjective (fun x : ℂ × ℂ => pack x.1 x.2) := by
  intro q
  exact ⟨(⟨q.re, q.imI⟩, ⟨-q.imJ, q.imK⟩), by ext <;> simp [pack_components]⟩

theorem pack_add (a b c d : ℂ) : pack (a + c) (b + d) = pack a b + pack c d := by
  simp [pack, mul_add]; abel

/-- Complex scalar multiplication on both entries corresponds to right multiplication in ℍ. -/
theorem pack_smul (z a b : ℂ) : pack (z * a) (z * b) = pack a b * (z : ℍ) := by
  simp only [pack, mul_comm z, Quaternion.coeComplex_mul, sub_mul, mul_assoc]

theorem pack_norm_sq (a b : ℂ) : ‖pack a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [sq, ← Quaternion.normSq_eq_norm_mul_self]
  simp [pack_components, Quaternion.normSq_def, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Ordinary quaternion coefficient row of A-jB. -/
def quaternionCoefficients (m : ℕ) (h : FormRow m) (k : Fin (m + 1)) : ℍ :=
  pack (coefficients m (h 0) k) (coefficients m (h 1) k)

theorem quaternionCoefficients_smul (m : ℕ) (z : ℂ) (h : FormRow m) (k : Fin (m + 1)) :
    quaternionCoefficients m (z • h) k = quaternionCoefficients m h k * (z : ℍ) := by
  simpa [quaternionCoefficients] using pack_smul z (coefficients m (h 0) k) (coefficients m (h 1) k)

/-- Every quaternion coefficient row is represented by exactly one pair (A,B). -/
theorem quaternionCoefficients_bijective (m : ℕ) : Function.Bijective (quaternionCoefficients m) := by
  constructor
  · intro h g hh
    apply PiLp.ext
    intro i
    apply coefficients_injective m
    funext k
    have he : (coefficients m (h 0) k, coefficients m (h 1) k) =
        (coefficients m (g 0) k, coefficients m (g 1) k) :=
      pack_injective (congrFun hh k)
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · intro q
    let a : Fin (m + 1) → ℂ := fun k => ⟨(q k).re, (q k).imI⟩
    let b : Fin (m + 1) → ℂ := fun k => ⟨-(q k).imJ, (q k).imK⟩
    let A := (coefficientEquiv m).symm a
    let B := (coefficientEquiv m).symm b
    have ha : coefficients m A = a := (coefficientEquiv m).apply_symm_apply a
    have hb : coefficients m B = b := (coefficientEquiv m).apply_symm_apply b
    refine ⟨WithLp.toLp 2 ![A, B], ?_⟩
    funext k
    change pack (coefficients m A k) (coefficients m B k) = q k
    rw [ha, hb, pack_components]
    ext <;> simp [a, b]

/-- The ambient row norm agrees with the wiki's quaternion coefficient norm. -/
theorem formRow_norm_sq (m : ℕ) (h : FormRow m) :
    ‖h‖ ^ 2 = ∑ k, ‖quaternionCoefficients m h k‖ ^ 2 / (m.choose k : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, binaryForm_norm_sq]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp [quaternionCoefficients, pack_norm_sq, add_div]

/-- Partial derivative as a map between the actual homogeneous polynomial spaces. -/
def derivative (m : ℕ) (i : Fin 2) : BinaryForm (m + 1) →ₗ[ℂ] BinaryForm m where
  toFun p := ⟨pderiv i (p : MvPolynomial (Fin 2) ℂ), by simpa using p.property.pderiv (i := i)⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- The normalized polynomial gradient (p_X/n, p_Y/n), with n=m+1. -/
def normalizedGradient (m : ℕ) : BinaryForm (m + 1) →ₗ[ℂ] CompatibleRow m where
  toFun p := ⟨WithLp.toLp 2 (fun i => ((m + 1 : ℂ)⁻¹) • derivative m i p), by
    change pderiv 1 ((m + 1 : ℂ)⁻¹ • pderiv 0 (p : MvPolynomial (Fin 2) ℂ)) =
      pderiv 0 ((m + 1 : ℂ)⁻¹ • pderiv 1 (p : MvPolynomial (Fin 2) ℂ))
    simp [pderiv_comm]⟩
  map_add' _ _ := by apply Subtype.ext; ext i; simp [smul_add]
  map_smul' _ _ := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    simp only [map_smul]
    exact smul_comm _ _ _

theorem complexToQuaternion_inv (z : ℂ) : ((z⁻¹ : ℂ) : ℍ) = (z : ℍ)⁻¹ :=
  map_inv₀ Quaternion.ofComplex z

/-- The normalized gradient really encodes (p_X-j p_Y)/n, coefficient by coefficient. -/
theorem normalizedGradient_quaternionCoefficients (m : ℕ) (p : BinaryForm (m + 1))
    (k : Fin (m + 1)) :
    quaternionCoefficients m (normalizedGradient m p) k =
      pack (coefficients m (derivative m 0 p) k) (coefficients m (derivative m 1 p) k) *
        (((m + 1 : ℂ)⁻¹) : ℍ) := by
  change pack (coefficients m ((m + 1 : ℂ)⁻¹ • derivative m 0 p) k)
    (coefficients m ((m + 1 : ℂ)⁻¹ • derivative m 1 p) k) = _
  simpa [complexToQuaternion_inv] using pack_smul (m + 1 : ℂ)⁻¹ (coefficients m (derivative m 0 p) k)
    (coefficients m (derivative m 1 p) k)

/-- The inverse candidate XA+YB, defined on all rows. -/
def assemble (m : ℕ) : FormRow m →ₗ[ℂ] BinaryForm (m + 1) where
  toFun h := ⟨X 0 * (h 0 : MvPolynomial (Fin 2) ℂ) + X 1 * (h 1 : MvPolynomial (Fin 2) ℂ), by
    apply IsHomogeneous.add
    · simpa [Nat.add_comm] using (isHomogeneous_X (R := ℂ) (0 : Fin 2)).mul (h 0).property
    · simpa [Nat.add_comm] using (isHomogeneous_X (R := ℂ) (1 : Fin 2)).mul (h 1).property⟩
  map_add' _ _ := by apply Subtype.ext; simp [mul_add]; ring
  map_smul' _ _ := by apply Subtype.ext; simp [smul_add]

theorem assemble_gradient (m : ℕ) (p : BinaryForm (m + 1)) :
    assemble m (normalizedGradient m p) = p := by
  apply Subtype.ext
  have he := p.property.sum_X_mul_pderiv
  simp only [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add, Nat.cast_one] at he
  change X 0 * ((m + 1 : ℂ)⁻¹ • pderiv 0 (p : MvPolynomial (Fin 2) ℂ)) +
    X 1 * ((m + 1 : ℂ)⁻¹ • pderiv 1 (p : MvPolynomial (Fin 2) ℂ)) = _
  rw [mul_smul_comm, mul_smul_comm, ← smul_add, he]
  have hn : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  exact inv_smul_smul₀ hn _

theorem derivative_assemble (m : ℕ) (h : CompatibleRow m) (i : Fin 2) :
    derivative m i (assemble m h) = (m + 1 : ℂ) • (h.val i) := by
  apply Subtype.ext
  have hc : pderiv 1 (h.val 0 : MvPolynomial (Fin 2) ℂ) =
      pderiv 0 (h.val 1 : MvPolynomial (Fin 2) ℂ) := h.property
  have he0 := (h.val 0).property.sum_X_mul_pderiv
  have he1 := (h.val 1).property.sum_X_mul_pderiv
  simp only [Fin.sum_univ_two, ← Nat.cast_smul_eq_nsmul ℂ] at he0 he1
  fin_cases i
  · change pderiv 0 (X 0 * (h.val 0 : MvPolynomial (Fin 2) ℂ) + X 1 * (h.val 1 : MvPolynomial (Fin 2) ℂ)) = (m + 1 : ℂ) • (h.val 0 : MvPolynomial (Fin 2) ℂ)
    simp only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0),
      one_mul, zero_mul, zero_add, ← hc, add_assoc]
    rw [he0, add_smul]; simp [add_comm]
  · change pderiv 1 (X 0 * (h.val 0 : MvPolynomial (Fin 2) ℂ) + X 1 * (h.val 1 : MvPolynomial (Fin 2) ℂ)) = (m + 1 : ℂ) • (h.val 1 : MvPolynomial (Fin 2) ℂ)
    simp only [map_add, pderiv_mul, pderiv_X_self, pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1),
      one_mul, zero_mul, zero_add, hc]
    rw [show X 0 * pderiv 0 (h.val 1 : MvPolynomial (Fin 2) ℂ) +
      ((h.val 1 : MvPolynomial (Fin 2) ℂ) + X 1 * pderiv 1 (h.val 1 : MvPolynomial (Fin 2) ℂ)) =
      (h.val 1 : MvPolynomial (Fin 2) ℂ) + (X 0 * pderiv 0 (h.val 1 : MvPolynomial (Fin 2) ℂ) +
      X 1 * pderiv 1 (h.val 1 : MvPolynomial (Fin 2) ℂ)) by ring, he1, add_smul]
    simp [add_comm]

theorem gradient_assemble (m : ℕ) (h : CompatibleRow m) :
    normalizedGradient m (assemble m h) = h := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  change (m + 1 : ℂ)⁻¹ • derivative m i (assemble m h) = h.val i
  rw [derivative_assemble, inv_smul_smul₀]
  exact_mod_cast Nat.succ_ne_zero m

/-- Algebraic isomorphism, before any assertion about norms. -/
def gradientEquiv (m : ℕ) : BinaryForm (m + 1) ≃ₗ[ℂ] CompatibleRow m :=
  { normalizedGradient m with
    invFun := fun h => assemble m h
    left_inv := assemble_gradient m
    right_inv := gradient_assemble m }

end MathResearch.Spinor
