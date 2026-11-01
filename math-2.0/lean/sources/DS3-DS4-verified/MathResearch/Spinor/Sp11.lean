module
public import MathResearch.Spinor.BallConnection
public import Mathlib.Tactic.NoncommRing

/-! The quaternionic matrix group and its ball/compact decomposition. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
namespace MathResearch.Spinor

/-- Jg*J, the adjoint for the Hermitian form of signature (1,1). -/
def signatureAdjoint (g : QuaternionMatrix2) : QuaternionMatrix2 :=
  !![star (g 0 0), -star (g 1 0); -star (g 0 1), star (g 1 1)]

def signatureMatrix : QuaternionMatrix2 := !![1, 0; 0, -1]

theorem signatureAdjoint_eq (g : QuaternionMatrix2) :
    signatureAdjoint g = signatureMatrix * g.conjTranspose * signatureMatrix := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [signatureAdjoint, signatureMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

@[simp] theorem signatureAdjoint_one : signatureAdjoint 1 = 1 := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [signatureAdjoint]

@[simp] theorem signatureAdjoint_involutive (g : QuaternionMatrix2) :
    signatureAdjoint (signatureAdjoint g) = g := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [signatureAdjoint]

@[simp] theorem signatureAdjoint_mul (g h : QuaternionMatrix2) :
    signatureAdjoint (g*h) = signatureAdjoint h * signatureAdjoint g := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [signatureAdjoint, Matrix.mul_apply, Fin.sum_univ_two] <;> abel

/-- The actual matrix equations defining Sp(1,1); both inverse identities are explicit. -/
def IsSp11 (g : QuaternionMatrix2) : Prop :=
  signatureAdjoint g * g = 1 ∧ g * signatureAdjoint g = 1

theorem IsSp11.mul {g h : QuaternionMatrix2} (hg : IsSp11 g) (hh : IsSp11 h) :
    IsSp11 (g*h) := by
  constructor
  · simp only [signatureAdjoint_mul]
    calc _ = signatureAdjoint h * (signatureAdjoint g * g) * h := by noncomm_ring
         _ = 1 := by rw [hg.1]; simpa using hh.1
  · simp only [signatureAdjoint_mul]
    calc _ = g * (h * signatureAdjoint h) * signatureAdjoint g := by noncomm_ring
         _ = 1 := by rw [hh.2]; simpa using hg.2

theorem isSp11_signatureAdjoint {g : QuaternionMatrix2} (hg : IsSp11 g) :
    IsSp11 (signatureAdjoint g) := by simpa [IsSp11] using And.intro hg.2 hg.1

theorem ballSection_isSp11 (q : ℍ) (hq : q ∈ Ball) : IsSp11 (ballSection q) := by
  have he : signatureAdjoint (ballSection q) = ballSectionInverse q := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      ext <;> simp [signatureAdjoint, ballSection, ballSectionInverse]
  simpa [IsSp11, he] using ballSection_inverse q hq

/-- Compact block-diagonal matrices. -/
def compactMatrix (a b : ℍ) : QuaternionMatrix2 := !![a, 0; 0, b]

theorem compactMatrix_mul (a b c d : ℍ) :
    compactMatrix a b * compactMatrix c d = compactMatrix (a*c) (b*d) := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [compactMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem compactMatrix_isSp11 (a b : ℍ) (ha : Quaternion.normSq a = 1)
    (hb : Quaternion.normSq b = 1) : IsSp11 (compactMatrix a b) := by
  constructor <;> apply Matrix.ext <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [signatureAdjoint, compactMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.star_mul_self, Quaternion.self_mul_star, ha, hb]

/-- The ball coordinate g·0=b d⁻¹. -/
def groupOrigin (g : QuaternionMatrix2) : ℍ := g 0 1 * (g 1 1)⁻¹

theorem IsSp11.column_norms {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Quaternion.normSq (g 0 0) - Quaternion.normSq (g 1 0) = 1 ∧
    Quaternion.normSq (g 1 1) - Quaternion.normSq (g 0 1) = 1 := by
  have h0 := congrArg (fun M : QuaternionMatrix2 => (M 0 0).re) hg.1
  have h1 := congrArg (fun M : QuaternionMatrix2 => (M 1 1).re) hg.1
  constructor
  · simpa [signatureAdjoint, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.normSq_def', pow_two, sub_eq_add_neg, mul_comm] using h0
  · simpa [signatureAdjoint, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.normSq_def', pow_two, sub_eq_add_neg, mul_comm, add_comm] using h1

theorem IsSp11.lowerRight_ne_zero {g : QuaternionMatrix2} (hg : IsSp11 g) : g 1 1 ≠ 0 := by
  intro h
  have := hg.column_norms.2
  rw [h, map_zero] at this
  nlinarith [(Quaternion.normSq_nonneg (a := g 0 1))]

theorem groupOrigin_scale {g : QuaternionMatrix2} (hg : IsSp11 g) :
    ballScale (groupOrigin g) = (Quaternion.normSq (g 1 1))⁻¹ := by
  have hd := Quaternion.normSq_ne_zero.mpr hg.lowerRight_ne_zero
  simp only [ballScale, groupOrigin, map_mul, map_inv₀]
  field_simp
  linarith [hg.column_norms.2]

theorem groupOrigin_mem_ball {g : QuaternionMatrix2} (hg : IsSp11 g) : groupOrigin g ∈ Ball := by
  change 0 < ballScale (groupOrigin g)
  rw [groupOrigin_scale hg]
  exact inv_pos.mpr (lt_of_le_of_ne (Quaternion.normSq_nonneg (a := g 1 1)) (Ne.symm (Quaternion.normSq_ne_zero.mpr hg.lowerRight_ne_zero)))

/-- The first column is (a,conj(q)a) in the ball chart. -/
theorem IsSp11.lowerLeft_eq {g : QuaternionMatrix2} (hg : IsSp11 g) :
    g 1 0 = star (groupOrigin g) * g 0 0 := by
  have hc : star (g 0 1) * g 0 0 = star (g 1 1) * g 1 0 := by
    have h := congrArg (fun M : QuaternionMatrix2 => M 1 0) hg.1
    have he : star (g 1 1) * g 1 0 - star (g 0 1) * g 0 0 = 0 := by
      simpa [signatureAdjoint, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg, add_comm] using h
    exact (sub_eq_zero.mp he).symm
  simp only [groupOrigin, star_mul, star_inv₀, mul_assoc, hc]
  rw [inv_mul_cancel_left₀ (star_ne_zero.mpr hg.lowerRight_ne_zero)]

/-- The two compact coordinates of g=σ(q)diag(kL,kR). -/
def compactLeft (g : QuaternionMatrix2) : ℍ := Real.sqrt (ballScale (groupOrigin g)) • g 0 0

def compactRight (g : QuaternionMatrix2) : ℍ := Real.sqrt (ballScale (groupOrigin g)) • g 1 1

theorem compactRight_unit {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Quaternion.normSq (compactRight g) = 1 := by
  rw [compactRight, Quaternion.normSq_smul, Real.sq_sqrt (le_of_lt (groupOrigin_mem_ball hg)), groupOrigin_scale hg]
  exact inv_mul_cancel₀ (Quaternion.normSq_ne_zero.mpr hg.lowerRight_ne_zero)

theorem compactLeft_unit {g : QuaternionMatrix2} (hg : IsSp11 g) :
    Quaternion.normSq (compactLeft g) = 1 := by
  have h := hg.column_norms.1
  rw [hg.lowerLeft_eq, map_mul, Quaternion.normSq_star] at h
  rw [compactLeft, Quaternion.normSq_smul, Real.sq_sqrt (le_of_lt (groupOrigin_mem_ball hg)), ballScale]
  nlinarith

/-- Every actual Sp(1,1) matrix has the section/compact factorization used by the wiki. -/
theorem section_compact_decomposition {g : QuaternionMatrix2} (hg : IsSp11 g) :
    g = ballSection (groupOrigin g) * compactMatrix (compactLeft g) (compactRight g) := by
  have hs : Real.sqrt (ballScale (groupOrigin g)) ≠ 0 := (Real.sqrt_pos.mpr (groupOrigin_mem_ball hg)).ne'
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ballSection, compactMatrix, compactLeft, compactRight, Matrix.mul_apply,
      Fin.sum_univ_two, smul_smul, hs]
  · simp [groupOrigin, hg.lowerRight_ne_zero]
  · exact hg.lowerLeft_eq

end MathResearch.Spinor
