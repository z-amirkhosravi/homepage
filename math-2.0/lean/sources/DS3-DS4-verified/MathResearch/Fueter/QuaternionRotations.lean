module
public import MathResearch.Fueter.PolynomialCalculus
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Unit quaternion pairs and the real rotation group of quaternion space. -/
@[expose] public section
noncomputable section
open scoped Quaternion BigOperators
namespace MathResearch.Fueter

abbrev UnitQuaternion := unitary ℍ
abbrev QuaternionSpinPair := UnitQuaternion × UnitQuaternion

theorem unitQuaternion_normSq (a : UnitQuaternion) : Quaternion.normSq (a : ℍ) = 1 := by
  have h := congrArg (fun q : ℍ => q.re) (Unitary.coe_star_mul_self a)
  simpa only [Quaternion.star_mul_self, Quaternion.re_coe, Quaternion.re_one] using h

theorem unitQuaternion_norm (a : UnitQuaternion) : ‖(a : ℍ)‖ = 1 := by
  have h := unitQuaternion_normSq a
  rw [Quaternion.normSq_eq_norm_mul_self] at h
  nlinarith [norm_nonneg (a : ℍ)]

@[simp] theorem unitQuaternion_coe_inv (a : UnitQuaternion) :
    ((a⁻¹ : UnitQuaternion) : ℍ) = star (a : ℍ) := rfl

/-- The forward rotation `(a,b) : q ↦ a q b⁻¹`. -/
def quaternionRotation (k : QuaternionSpinPair) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun q := (k.1 : ℍ) * q * star (k.2 : ℍ)
  invFun q := star (k.1 : ℍ) * q * (k.2 : ℍ)
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' t x := by simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
  left_inv q := by
    change star (k.1 : ℍ) * ((k.1 : ℍ) * q * star (k.2 : ℍ)) * (k.2 : ℍ) = q
    calc
      _ = (star (k.1 : ℍ) * (k.1 : ℍ)) * q * (star (k.2 : ℍ) * (k.2 : ℍ)) := by noncomm_ring
      _ = q := by rw [Unitary.coe_star_mul_self, Unitary.coe_star_mul_self, one_mul, mul_one]
  right_inv q := by
    change (k.1 : ℍ) * (star (k.1 : ℍ) * q * (k.2 : ℍ)) * star (k.2 : ℍ) = q
    calc
      _ = ((k.1 : ℍ) * star (k.1 : ℍ)) * q * ((k.2 : ℍ) * star (k.2 : ℍ)) := by noncomm_ring
      _ = q := by simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, one_mul, mul_one]
  norm_map' q := by
    change ‖(k.1 : ℍ) * q * star (k.2 : ℍ)‖ = ‖q‖
    simp only [norm_mul, norm_star, unitQuaternion_norm, one_mul, mul_one]

@[simp] theorem quaternionRotation_apply (k : QuaternionSpinPair) (q : ℍ) :
    quaternionRotation k q = (k.1 : ℍ) * q * star (k.2 : ℍ) := rfl

@[simp] theorem quaternionRotation_one : quaternionRotation 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro q
  simp [quaternionRotation]

theorem quaternionRotation_mul (k l : QuaternionSpinPair) :
    quaternionRotation (k * l) = quaternionRotation k * quaternionRotation l := by
  apply LinearIsometryEquiv.ext
  intro q
  simp [quaternionRotation, star_mul, mul_assoc]

def quaternionRotationHom : QuaternionSpinPair →* (ℍ ≃ₗᵢ[ℝ] ℍ) where
  toFun := quaternionRotation
  map_one' := quaternionRotation_one
  map_mul' := quaternionRotation_mul

@[simp] theorem quaternionRotation_inv (k : QuaternionSpinPair) :
    quaternionRotation k⁻¹ = (quaternionRotation k).symm :=
  map_inv quaternionRotationHom k

/-- SO(4) in its basis-independent realization on the four-dimensional real
quaternion inner-product space: the isometries of determinant one. -/
def quaternionIsometryDet : (ℍ ≃ₗᵢ[ℝ] ℍ) →* ℝˣ where
  toFun e := LinearEquiv.det e.toLinearEquiv
  map_one' := map_one LinearEquiv.det
  map_mul' e f := by
    change LinearEquiv.det (e.toLinearEquiv * f.toLinearEquiv) = _
    exact map_mul LinearEquiv.det _ _

abbrev QuaternionSO4 := quaternionIsometryDet.ker

def quaternionMulLeft (a : ℍ) : ℍ →ₗ[ℝ] ℍ where
  toFun q := a * q
  map_add' := mul_add a
  map_smul' t q := by simp only [RingHom.id_apply, mul_smul_comm]

def quaternionMulRight (a : ℍ) : ℍ →ₗ[ℝ] ℍ where
  toFun q := q * a
  map_add' x y := add_mul x y a
  map_smul' t q := by simp only [RingHom.id_apply, smul_mul_assoc]

def quaternionConj : ℍ ≃ₗᵢ[ℝ] ℍ where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_add' := star_add
  map_smul' t q := Quaternion.star_smul t q
  norm_map' := norm_star

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem det_quaternionMulLeft (a : ℍ) :
    LinearMap.det (quaternionMulLeft a) = Quaternion.normSq a ^ 2 := by
  rw [← LinearMap.det_toMatrix coordinateBasis, Matrix.det_succ_row_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, coordinateBasis_eq]
  norm_num [Fin.succAbove, quaternionMulLeft, coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr, Quaternion.normSq_def']
  ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
theorem det_quaternionMulRight (a : ℍ) :
    LinearMap.det (quaternionMulRight a) = Quaternion.normSq a ^ 2 := by
  rw [← LinearMap.det_toMatrix coordinateBasis, Matrix.det_succ_row_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, coordinateBasis_eq]
  norm_num [Fin.succAbove, quaternionMulRight, coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr, Quaternion.normSq_def']
  ring

theorem det_quaternionConj : LinearMap.det quaternionConj.toLinearEquiv.toLinearMap = -1 := by
  rw [← LinearMap.det_toMatrix coordinateBasis, Matrix.det_succ_row_zero]
  simp only [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply, coordinateBasis_eq]
  norm_num [Fin.succAbove, quaternionConj, coordinateBasis,
    QuaternionAlgebra.coe_basisOneIJK_repr]

theorem quaternionRotation_det (k : QuaternionSpinPair) :
    quaternionIsometryDet (quaternionRotation k) = 1 := by
  apply Units.ext
  change ↑(LinearEquiv.det (quaternionRotation k).toLinearEquiv) = (1 : ℝ)
  rw [LinearEquiv.coe_det]
  have h : (quaternionRotation k).toLinearEquiv.toLinearMap =
      (quaternionMulRight (star (k.2 : ℍ))).comp (quaternionMulLeft (k.1 : ℍ)) := rfl
  rw [h, LinearMap.det_comp, det_quaternionMulLeft, det_quaternionMulRight,
    Quaternion.normSq_star, unitQuaternion_normSq, unitQuaternion_normSq]
  norm_num

/-- The usual homomorphism Spin(4) → SO(4). Surjectivity is proved below. -/
def quaternionSpinCover : QuaternionSpinPair →* QuaternionSO4 :=
  quaternionRotationHom.codRestrict _ quaternionRotation_det

@[simp] theorem quaternionSpinCover_coe (k : QuaternionSpinPair) :
    (quaternionSpinCover k : ℍ ≃ₗᵢ[ℝ] ℍ) = quaternionRotation k := rfl

theorem unitQuaternion_reflection (u : UnitQuaternion) (q : ℍ) :
    (ℝ ∙ (u : ℍ))ᗮ.reflection q = -(u : ℍ) * star q * (u : ℍ) := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    unitQuaternion_norm]
  norm_num
  have h := congrArg (fun x : ℍ => x * (u : ℍ)) (Quaternion.self_add_star' ((u : ℍ) * star q))
  simp only [add_mul, star_mul, star_star, mul_assoc, Unitary.coe_star_mul_self, mul_one,
    Quaternion.coe_mul_eq_smul, ← Quaternion.inner_def] at h
  simp only [mul_smul, two_smul, ← mul_assoc] at h
  rw [two_mul, smul_add, ← h]
  abel

/-- Normalize a nonzero quaternion to a unit quaternion. -/
def normalizeQuaternion (v : ℍ) (hv : v ≠ 0) : UnitQuaternion := by
  refine ⟨‖v‖⁻¹ • v, ?_⟩
  have hn : Quaternion.normSq (‖v‖⁻¹ • v) = 1 := by
    rw [Quaternion.normSq_smul, Quaternion.normSq_eq_norm_mul_self]
    field_simp
  constructor
  · rw [Quaternion.star_mul_self, hn, Quaternion.coe_one]
  · rw [Quaternion.self_mul_star, hn, Quaternion.coe_one]

theorem reflection_as_rotation_conj (v : ℍ) (hv : v ≠ 0) :
    (ℝ ∙ v)ᗮ.reflection =
      quaternionRotation (-normalizeQuaternion v hv, (normalizeQuaternion v hv)⁻¹) *
        quaternionConj := by
  have hspan : ℝ ∙ (normalizeQuaternion v hv : ℍ) = ℝ ∙ v :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v
  apply LinearIsometryEquiv.ext
  intro q
  have h := unitQuaternion_reflection (normalizeQuaternion v hv) q
  simpa [hspan, quaternionRotation, quaternionConj, Unitary.coe_neg] using h

theorem quaternionConj_rotation (k : QuaternionSpinPair) :
    quaternionConj * quaternionRotation k = quaternionRotation (k.2, k.1) * quaternionConj := by
  apply LinearIsometryEquiv.ext
  intro q
  simp [quaternionConj, quaternionRotation, star_mul, mul_assoc]

@[simp] theorem quaternionConj_sq : quaternionConj * quaternionConj = 1 := by
  apply LinearIsometryEquiv.ext
  intro q
  exact star_star q

/-- Cartan–Dieudonné gives the quaternionic forms of every orthogonal transformation. -/
theorem quaternionIsometry_forms (e : ℍ ≃ₗᵢ[ℝ] ℍ) :
    (∃ k, e = quaternionRotation k) ∨
      (∃ k, e = quaternionRotation k * quaternionConj) := by
  obtain ⟨l, hlen, rfl⟩ := e.reflections_generate_dim
  clear hlen
  induction l with
  | nil => exact Or.inl ⟨1, quaternionRotation_one.symm⟩
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hv : v = 0
    · subst v
      have hz : (ℝ ∙ (0 : ℍ))ᗮ.reflection = 1 := by
        apply LinearIsometryEquiv.ext
        intro q
        simp only [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
        norm_num
      rw [hz, one_mul]
      exact ih
    rw [reflection_as_rotation_conj v hv]
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      refine ⟨(-normalizeQuaternion v hv, (normalizeQuaternion v hv)⁻¹) * (k.2, k.1), ?_⟩
      rw [hk, mul_assoc, quaternionConj_rotation, ← mul_assoc, ← quaternionRotation_mul]
    · left
      refine ⟨(-normalizeQuaternion v hv, (normalizeQuaternion v hv)⁻¹) * (k.2, k.1), ?_⟩
      rw [hk, ← mul_assoc, mul_assoc (quaternionRotation _), quaternionConj_rotation]
      simp only [← mul_assoc, ← quaternionRotation_mul]
      rw [mul_assoc, quaternionConj_sq, mul_one]

theorem quaternionSpinCover_surjective : Function.Surjective quaternionSpinCover := by
  intro e
  rcases quaternionIsometry_forms e.val with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k, Subtype.ext hk.symm⟩
  · have hd := e.property
    change quaternionIsometryDet e.val = 1 at hd
    rw [hk, map_mul, quaternionRotation_det, one_mul] at hd
    have hc := congrArg (fun u : ℝˣ => (u : ℝ)) hd
    change ↑(LinearEquiv.det quaternionConj.toLinearEquiv) = (1 : ℝ) at hc
    rw [LinearEquiv.coe_det, det_quaternionConj] at hc
    norm_num at hc

/-- The kernel of the spin covering consists of the simultaneous signs. -/
theorem quaternionRotation_kernel (k : QuaternionSpinPair)
    (hk : quaternionRotation k = 1) : k = 1 ∨ k = (-1, -1) := by
  have hq (q : ℍ) : (k.1 : ℍ) * q * star (k.2 : ℍ) = q :=
    congrArg (fun e : ℍ ≃ₗᵢ[ℝ] ℍ => e q) hk
  have hab : (k.1 : ℍ) = (k.2 : ℍ) := by
    have h := congrArg (fun q : ℍ => q * (k.2 : ℍ)) (hq 1)
    simpa only [mul_one,
      mul_assoc, Unitary.coe_star_mul_self, one_mul] using h
  have hcomm (q : ℍ) : (k.1 : ℍ) * q = q * (k.1 : ℍ) := by
    have h := congrArg (fun p : ℍ => p * (k.2 : ℍ)) (hq q)
    simpa only [mul_assoc,
      Unitary.coe_star_mul_self, mul_one, ← hab] using h
  have hj : (k.1 : ℍ).imJ = 0 := by
    have h := congrArg (fun q : ℍ => q.imK) (hcomm ⟨0, 1, 0, 0⟩)
    simp at h
    linarith
  have hk' : (k.1 : ℍ).imK = 0 := by
    have h := congrArg (fun q : ℍ => q.imJ) (hcomm ⟨0, 1, 0, 0⟩)
    simp at h
    linarith
  have hi : (k.1 : ℍ).imI = 0 := by
    have h := congrArg (fun q : ℍ => q.imK) (hcomm ⟨0, 0, 1, 0⟩)
    simp at h
    linarith
  have hn := unitQuaternion_normSq k.1
  rw [Quaternion.normSq_def', hi, hj, hk'] at hn
  have hre : (k.1 : ℍ).re = 1 ∨ (k.1 : ℍ).re = -1 := by
    have hsq : ((k.1 : ℍ).re - 1) * ((k.1 : ℍ).re + 1) = 0 := by nlinarith [hn]
    rcases mul_eq_zero.mp hsq with h | h
    · left; linarith
    · right; linarith
  rcases hre with hre | hre
  · left
    have ha : k.1 = 1 := Subtype.ext (by ext <;> simp [hre, hi, hj, hk'])
    have hb : k.2 = 1 := Subtype.ext (by rw [← hab]; exact congrArg Subtype.val ha)
    exact Prod.ext ha hb
  · right
    have ha : k.1 = -1 := Subtype.ext (by change (k.1 : ℍ) = (-1 : ℍ); ext <;> simp [hre, hi, hj, hk'])
    have hb : k.2 = -1 := Subtype.ext (by rw [← hab]; exact congrArg Subtype.val ha)
    exact Prod.ext ha hb

end MathResearch.Fueter
