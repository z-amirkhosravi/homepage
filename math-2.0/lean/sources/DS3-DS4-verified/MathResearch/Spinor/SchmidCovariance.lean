module
public import MathResearch.Spinor.SchmidFueter
public import MathResearch.Spinor.OrthonormalContraction

/-! Compact-frame covariance and the global smooth kernel correspondence. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators Matrix.Norms.Elementwise
open MvPolynomial
namespace MathResearch.Spinor

abbrev PolynomialColumn := Fin 2 → ComplexPoly2

def spinorProjection (n : ℕ) (v : ℍ) (p : BinaryForm n) : PolynomialColumn :=
  matrixColumn (quaternionMatrix v) (fun i => pderiv i (p : ComplexPoly2))

theorem matrixColumn_mul (M N : Matrix2) (h : PolynomialColumn) :
    matrixColumn (M*N) h = matrixColumn M (matrixColumn N h) := by
  funext i
  simp [matrixColumn, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp] theorem matrixColumn_one (h : PolynomialColumn) : matrixColumn 1 h = h := by
  funext i; fin_cases i <;> simp [matrixColumn, Matrix.one_apply]

theorem spinorProjection_add_right (n : ℕ) (v : ℍ) (p r : BinaryForm n) :
    spinorProjection n v (p+r) = spinorProjection n v p + spinorProjection n v r := by
  funext i; simp [spinorProjection, matrixColumn]; ring

theorem spinorProjection_smul_right (n : ℕ) (v : ℍ) (r : ℝ) (p : BinaryForm n) :
    spinorProjection n v (r • p) = r • spinorProjection n v p := by
  change spinorProjection n v ((r:ℂ) • p) = (r:ℂ) • spinorProjection n v p
  funext i; simp [spinorProjection, matrixColumn, smul_add]

theorem spinorProjection_add_left (n : ℕ) (v w : ℍ) (p : BinaryForm n) :
    spinorProjection n (v+w) p = spinorProjection n v p + spinorProjection n w p := by
  funext i; simp [spinorProjection, matrixColumn, quaternionMatrix_add]; ring

theorem spinorProjection_smul_left (n : ℕ) (r : ℝ) (v : ℍ) (p : BinaryForm n) :
    spinorProjection n (r • v) p = r • spinorProjection n v p := by
  change spinorProjection n (r • v) p = (r:ℂ) • spinorProjection n v p
  funext i; simp [spinorProjection, matrixColumn, quaternionMatrix_real_smul, smul_eq_C_mul]; ring

/-- The real bilinear symbol v⊗p ↦ vT_np. -/
def projectionSymbol (n : ℕ) : ℍ →ₗ[ℝ] BinaryForm n →ₗ[ℝ] PolynomialColumn where
  toFun v :=
    { toFun := spinorProjection n v
      map_add' := spinorProjection_add_right n v
      map_smul' := spinorProjection_smul_right n v }
  map_add' v w := by apply LinearMap.ext; intro p; exact spinorProjection_add_left n v w p
  map_smul' r v := by apply LinearMap.ext; intro p; exact spinorProjection_smul_left n r v p

/-- Polynomial substitution on both components of a column. -/
def columnSubstitution (u : ℍ) (h : PolynomialColumn) : PolynomialColumn :=
  fun i => polynomialAction (quaternionMatrix u) (h i)

theorem columnSubstitution_matrixColumn (u : ℍ) (M : Matrix2) (h : PolynomialColumn) :
    columnSubstitution u (matrixColumn M h) = matrixColumn M (columnSubstitution u h) := by
  funext i; simp [columnSubstitution, matrixColumn]

/-- The exact chain rule for the projection and polynomial action. -/
theorem spinorProjection_action (n : ℕ) (u v : ℍ) (p : BinaryForm n) :
    spinorProjection n v (polynomialRepresentation n (quaternionMatrix u) p) =
      columnSubstitution u (spinorProjection n (v*u) p) := by
  change matrixColumn (quaternionMatrix v)
      (fun i => pderiv i (polynomialAction (quaternionMatrix u) p)) = _
  simp_rw [polynomialAction_chainRule]
  change matrixColumn (quaternionMatrix v)
      (matrixColumn (quaternionMatrix u) (columnSubstitution u (fun i => pderiv i (p : ComplexPoly2)))) = _
  rw [← matrixColumn_mul, ← quaternionMatrix_mul]
  exact (columnSubstitution_matrixColumn u _ _).symm

/-- Projection of a real linear differential, as a polynomial column. -/
def projectedLinear (n : ℕ) (L : ℍ →ₗ[ℝ] BinaryForm n) : PolynomialColumn :=
  ∑ μ : Fin 4, spinorProjection n (Fueter.coordinateBasis μ) (L (Fueter.coordinateBasis μ))

theorem projectedLinear_rotation (n : ℕ) (L : ℍ →ₗ[ℝ] BinaryForm n) (R : ℍ ≃ₗᵢ[ℝ] ℍ) :
    (∑ μ : Fin 4, spinorProjection n (R (Fueter.coordinateBasis μ)) (L (R (Fueter.coordinateBasis μ)))) =
      projectedLinear n L := by
  let B : ℍ →ₗ[ℝ] ℍ →ₗ[ℝ] PolynomialColumn :=
    { toFun := fun v => (projectionSymbol n v).comp L
      map_add' := by intro v w; apply LinearMap.ext; intro x; exact spinorProjection_add_left n v w (L x)
      map_smul' := by intro r v; apply LinearMap.ext; intro x; exact spinorProjection_smul_left n r v (L x) }
  exact quaternion_contraction_rotation R B

/-- Real continuous polynomial action for a fixed quaternion. -/
def realQuaternionAction (n : ℕ) (a : ℍ) : BinaryForm n →L[ℝ] BinaryForm n :=
  ((polynomialRepresentation n (quaternionMatrix a)).restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem realQuaternionAction_apply (n : ℕ) (a : ℍ) (p : BinaryForm n) :
    realQuaternionAction n a p = polynomialRepresentation n (quaternionMatrix a) p := rfl

theorem unitQuaternion_ne_zero (b : Fueter.UnitQuaternion) : (b : ℍ) ≠ 0 := by
  intro h
  have := Fueter.unitQuaternion_normSq b
  simp [h] at this

theorem unitQuaternion_inv (b : Fueter.UnitQuaternion) : (b : ℍ)⁻¹ = star (b : ℍ) := by
  apply inv_eq_of_mul_eq_one_right
  exact Unitary.coe_mul_star_self b

/-- The adjoint action of diag(a,b) sends ξ_v to ξ_(avb⁻¹). -/
theorem compact_tangent (k : Fueter.QuaternionSpinPair) (v : ℍ) :
    compactMatrix k.1 k.2 * tangentMatrix v =
      tangentMatrix (Fueter.quaternionRotation k v) * compactMatrix k.1 k.2 := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp [compactMatrix, tangentMatrix, Fueter.quaternionRotation_apply,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem rightAffinePath_compact (g : QuaternionMatrix2) (k : Fueter.QuaternionSpinPair) (v : ℍ) (t : ℝ) :
    rightAffinePath (g * compactMatrix k.1 k.2) v t =
      rightAffinePath g (Fueter.quaternionRotation k v) t * compactMatrix k.1 k.2 := by
  simp only [rightAffinePath, add_mul, smul_mul_assoc]
  congr 1
  rw [mul_assoc, compact_tangent k v, ← mul_assoc]

theorem rightLieDerivative_frameLift_compact (n : ℕ) (U : ℍ → BinaryForm n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) (hU : DifferentiableAt ℝ U (groupOrigin g))
    (k : Fueter.QuaternionSpinPair) (v : ℍ) :
    rightLieDerivative n (frameLift n U) (g * compactMatrix k.1 k.2) v =
      realQuaternionAction n (star (k.2 : ℍ))
        (rightLieDerivative n (frameLift n U) g (Fueter.quaternionRotation k v)) := by
  have hf := differentiableAt_frameLift n U hg hU
  have hd := (show HasFDerivAt (frameLift n U) (fderiv ℝ (frameLift n U) g)
      (rightAffinePath g (Fueter.quaternionRotation k v) 0) from by simpa using hf.hasFDerivAt).comp_hasDerivAt 0
        (rightAffinePath_hasDerivAt g (Fueter.quaternionRotation k v))
  have he : (fun t => frameLift n U (rightAffinePath (g * compactMatrix k.1 k.2) v t)) =
      fun t => realQuaternionAction n (star (k.2 : ℍ)) (frameLift n U (rightAffinePath g (Fueter.quaternionRotation k v) t)) := by
    funext t
    rw [rightAffinePath_compact, frameLift_equivariant n U _ _ _ (unitQuaternion_ne_zero k.2), unitQuaternion_inv]
    rfl
  rw [rightLieDerivative, he, rightLieDerivative_eq_fderiv n _ _ hf]
  exact ((realQuaternionAction n (star (k.2 : ℍ))).hasFDerivAt.comp_hasDerivAt 0 hd).deriv

/-- Target transformation associated with the compact frame change. -/
def compactTarget (k : Fueter.QuaternionSpinPair) (h : PolynomialColumn) : PolynomialColumn :=
  matrixColumn (quaternionMatrix (star (k.1 : ℍ))) (columnSubstitution (star (k.2 : ℍ)) h)

@[simp] theorem compactTarget_zero (k : Fueter.QuaternionSpinPair) : compactTarget k 0 = 0 := by
  funext i; simp [compactTarget, matrixColumn, columnSubstitution]

theorem compactTarget_sum (k : Fueter.QuaternionSpinPair) {ι : Type*} (s : Finset ι)
    (h : ι → PolynomialColumn) : compactTarget k (∑ i ∈ s, h i) = ∑ i ∈ s, compactTarget k (h i) := by
  funext i
  simp [compactTarget, columnSubstitution, matrixColumn, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The symbol's K-equivariance, with the exact column and left/right conventions. -/
theorem spinorProjection_compact (n : ℕ) (k : Fueter.QuaternionSpinPair) (v : ℍ) (p : BinaryForm n) :
    spinorProjection n v (realQuaternionAction n (star (k.2 : ℍ)) p) =
      compactTarget k (spinorProjection n (Fueter.quaternionRotation k v) p) := by
  rw [realQuaternionAction_apply, spinorProjection_action, compactTarget]
  simp only [spinorProjection, columnSubstitution_matrixColumn]
  change matrixColumn (quaternionMatrix (v * star (k.2 : ℍ))) _ =
      matrixColumn (quaternionMatrix (star (k.1 : ℍ)))
        (matrixColumn (quaternionMatrix (Fueter.quaternionRotation k v)) _) 
  rw [← matrixColumn_mul, ← quaternionMatrix_mul]
  congr 1
  simp [Fueter.quaternionRotation_apply, ← mul_assoc]

/-- The projected group derivative in complex polynomial columns. -/
def projectedGroupColumn (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n) (g : QuaternionMatrix2) : PolynomialColumn :=
  ∑ μ : Fin 4, spinorProjection n (Fueter.coordinateBasis μ)
    (rightLieDerivative n F g (Fueter.coordinateBasis μ))

theorem projectedGroupColumn_compact (n : ℕ) (U : ℍ → BinaryForm n)
    {g : QuaternionMatrix2} (hg : IsSp11 g) (hU : DifferentiableAt ℝ U (groupOrigin g))
    (k : Fueter.QuaternionSpinPair) :
    projectedGroupColumn n (frameLift n U) (g * compactMatrix k.1 k.2) =
      compactTarget k (projectedGroupColumn n (frameLift n U) g) := by
  have hf := differentiableAt_frameLift n U hg hU
  let L : ℍ →ₗ[ℝ] BinaryForm n :=
    (fderiv ℝ (frameLift n U) g).toLinearMap.comp
      ((LinearMap.mulLeft ℝ g).comp tangentCLM.toLinearMap)
  have hL (v : ℍ) : L v = rightLieDerivative n (frameLift n U) g v := by
    rw [rightLieDerivative_eq_fderiv n _ _ hf]
    rfl
  simp only [projectedGroupColumn, rightLieDerivative_frameLift_compact n U hg hU,
    spinorProjection_compact, ← compactTarget_sum]
  congr 1
  simpa only [hL, projectedLinear] using projectedLinear_rotation n L (Fueter.quaternionRotation k)

/-- The column and quaternion coefficient versions of the projected operator agree. -/
theorem projectedGroupOperator_pack (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) (d : Fin 2 →₀ ℕ) :
    projectedGroupOperator n F g d =
      pack ((projectedGroupColumn n F g 0).coeff d) ((projectedGroupColumn n F g 1).coeff d) := by
  simp [projectedGroupOperator, projectedGroupColumn, spinorProjection,
    pack_sum, matrixColumn_pack_coeff, polynomialFueterCoefficients]

theorem projectedGroupColumn_zero_iff (n : ℕ) (F : QuaternionMatrix2 → BinaryForm n)
    (g : QuaternionMatrix2) : projectedGroupColumn n F g = 0 ↔ ∀ d, projectedGroupOperator n F g d = 0 := by
  constructor
  · intro h d; simp [projectedGroupOperator_pack, h, pack]
  · intro h
    funext i
    apply MvPolynomial.ext
    intro d
    have he : (((projectedGroupColumn n F g 0).coeff d), ((projectedGroupColumn n F g 1).coeff d)) = (0,0) := by
      apply pack_injective
      simpa [projectedGroupOperator_pack, pack] using h d
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

/-- Convert the proved norm equation into mathlib's unit quaternion group. -/
def unitOfNormSq (a : ℍ) (ha : Quaternion.normSq a = 1) : Fueter.UnitQuaternion :=
  ⟨a, by constructor <;> simp [Quaternion.star_mul_self, Quaternion.self_mul_star, ha]⟩

/-- Vanishing on the section extends to all of G by the proved K-covariance. -/
theorem group_kernel_iff_section (n : ℕ) (U : ℍ → BinaryForm n)
    (hU : ∀ q ∈ Ball, DifferentiableAt ℝ U q) :
    (∀ g, IsSp11 g → ∀ d, projectedGroupOperator n (frameLift n U) g d = 0) ↔
    (∀ q ∈ Ball, ∀ d, projectedGroupOperator n (frameLift n U) (ballSection q) d = 0) := by
  constructor
  · intro h q hq; exact h (ballSection q) (ballSection_isSp11 q hq)
  · intro h g hg
    let k : Fueter.QuaternionSpinPair :=
      (unitOfNormSq (compactLeft g) (compactLeft_unit hg), unitOfNormSq (compactRight g) (compactRight_unit hg))
    have hq := groupOrigin_mem_ball hg
    have hd : DifferentiableAt ℝ U (groupOrigin (ballSection (groupOrigin g))) := by
      simpa [groupOrigin_ballSection _ hq] using hU (groupOrigin g) hq
    have he := projectedGroupColumn_compact n U (ballSection_isSp11 _ hq) hd k
    have hz := (projectedGroupColumn_zero_iff n (frameLift n U) (ballSection (groupOrigin g))).mpr (h _ hq)
    rw [hz, compactTarget_zero] at he
    change projectedGroupColumn n (frameLift n U)
      (ballSection (groupOrigin g) * compactMatrix (compactLeft g) (compactRight g)) = 0 at he
    rw [← section_compact_decomposition hg] at he
    exact (projectedGroupColumn_zero_iff n (frameLift n U) g).mp he

/-- SC3/v1: the exact weighted formula and global group/ball kernel equivalence, all n≥1. -/
theorem SC3_frameLift_v1 (n : ℕ) (hn : 1 ≤ n) (f : ℍ → BinaryForm n)
    (hf : ∀ q ∈ Ball, DifferentiableAt ℝ f q) :
    (∀ q ∈ Ball, ∀ d,
      (24 : ℝ) • schmidOperator n (frameLift n (weightedSpinor n f)) (ballSection q) d =
        ballWeight (((n:ℝ)+4)/2) q •
          Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q) ∧
    ((∀ g, IsSp11 g → ∀ d, schmidOperator n (frameLift n (weightedSpinor n f)) g d = 0) ↔
      (∀ q ∈ Ball, ∀ d, Fueter.leftOperator (fun x => fueterCoefficientCLM n d (f x)) q = 0)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hU : ∀ q ∈ Ball, DifferentiableAt ℝ (weightedSpinor (m+1) f) q := by
    intro q hq
    exact ((hasFDerivAt_ballWeight _ hq).smul (hf q hq).hasFDerivAt).differentiableAt
  have hs (q : ℍ) (hq : q ∈ Ball) (d : Fin 2 →₀ ℕ) := SC3_v1_coefficients m f q hq (hf q hq) d
  constructor
  · intro q hq d
    rw [schmidOperator_normalization]
    exact hs q hq d
  · simp only [schmidOperator, smul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    rw [group_kernel_iff_section (m+1) _ hU]
    apply forall_congr'; intro q
    apply forall_congr'; intro hq
    apply forall_congr'; intro d
    rw [hs q hq d]
    exact smul_eq_zero_iff_right (ne_of_gt (ballWeight_pos _ hq))

end MathResearch.Spinor
