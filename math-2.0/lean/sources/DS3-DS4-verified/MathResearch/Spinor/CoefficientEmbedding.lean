module
public import MathResearch.Spinor.WeightedMeasure
public import Mathlib.Topology.MetricSpace.Isometry

/-! DS4's coefficient calculation with explicit Haar-disintegration and Schur inputs.
The formula uses mathlib's inner product, linear in the second argument. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion BigOperators ENNReal
open MeasureTheory
namespace MathResearch.Spinor

instance sp11TopologicalSpace : TopologicalSpace Sp11 :=
  inferInstanceAs (TopologicalSpace {g : QuaternionMatrix2 // IsSp11 g})
instance sp11MeasurableSpace : MeasurableSpace Sp11 := borel Sp11
instance sp11BorelSpace : BorelSpace Sp11 := ⟨rfl⟩

abbrev CompactPair := Fueter.QuaternionSpinPair

def compactSp11 (k : CompactPair) : Sp11 :=
  ⟨compactMatrix k.1 k.2, compactMatrix_isSp11 _ _
    (Fueter.unitQuaternion_normSq _) (Fueter.unitQuaternion_normSq _)⟩

/-- The lifted coefficient ⟨F_f(g),v⟩ in the wiki's linear-first convention. -/
def liftedCoefficient (n : ℕ) (v : BinaryForm n) (f : ℍ → BinaryForm n) (g : Sp11) : ℂ :=
  inner ℂ v (fullLift n f g)

/-- The C12 intertwining formula, for all functions, without analytic assumptions. -/
theorem liftedCoefficient_intertwines (n : ℕ) (v : BinaryForm n) (f : ℍ → BinaryForm n)
    (a g : Sp11) :
    liftedCoefficient n v (ballRepresentation n a f) g = liftedCoefficient n v f (a⁻¹*g) := by
  unfold liftedCoefficient ballRepresentation
  rw [fullLift_ballAction n f (isSp11_signatureAdjoint a.property) g.property]
  rfl

/-- Schur orthogonality for the specific degree-n compact polynomial representation.
This is an explicit external input, not an axiom or a proved instance. -/
def CompactSchurInput (n : ℕ) (μK : Measure CompactPair) : Prop :=
  ∀ u v : BinaryForm n,
    (∫ k, ‖inner ℂ v (polynomialRepresentation n (quaternionMatrix ((k.2 : ℍ)⁻¹)) u)‖^2 ∂μK) =
      ‖u‖^2 * ‖v‖^2 / (n+1:ℝ)

theorem fullLift_section_compact (n : ℕ) (f : ℍ → BinaryForm n) (q : ℍ) (hq : q ∈ Ball)
    (k : CompactPair) :
    fullLift n f (ballSection q * (compactSp11 k : QuaternionMatrix2)) =
      polynomialRepresentation n (quaternionMatrix ((k.2 : ℍ)⁻¹)) (weightedSpinor n f q) := by
  change fullLift n f (ballSection q * compactMatrix (k.1 : ℍ) (k.2 : ℍ)) = _
  rw [fullLift_rightEquivariant n f (ballSection q) (ballSection_isSp11 q hq) _ _
    (Fueter.unitQuaternion_normSq _) (Fueter.unitQuaternion_normSq _), fullLift_section n f q hq]

/-- The radial exponent in DS4 cancels exactly, including at the minimal degree n=2. -/
theorem lift_weight_cancellation (n : ℕ) (hn : 2 ≤ n) (q : ℍ) (hq : q ∈ Ball) :
    (ballScale q)⁻¹ ^ 4 * (ballWeight (((n:ℝ)+2)/2) q)^2 = (ballScale q)^(n-2) := by
  unfold ballWeight
  rw [← Real.rpow_mul_natCast hq.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (((n:ℝ)+2)/2)*(2:ℝ)=(n:ℝ)+2 by ring,
    show (n:ℝ)+2=((n+2:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [show n+2=4+(n-2) by omega, pow_add]
  have hs : 0 < ballScale q := hq
  field_simp [hs.ne']

/-- Haar disintegration for this coefficient, written before either Schur or radial cancellation.
Integrability is tracked separately; this equality alone does not assert square-integrability. -/
def CoefficientHaarInput (n : ℕ) (μG : Measure Sp11) (μK : Measure CompactPair)
    (v : BinaryForm n) (f : ℍ → BinaryForm n) : Prop :=
  (∫ g, ‖liftedCoefficient n v f g‖^2 ∂μG) =
    ∫ q in Ball, (ballScale q)⁻¹ ^ 4 *
      ∫ k, ‖inner ℂ v (fullLift n f (ballSection q * (compactSp11 k : QuaternionMatrix2)))‖^2 ∂μK

/-- DS4's exact C13 constant is derived from the two displayed integral inputs,
not assumed as a norm identity. -/
theorem DS4_coefficient_integral_of_haar_schur (n : ℕ) (hn : 2 ≤ n)
    (μG : Measure Sp11) (μK : Measure CompactPair) (hSchur : CompactSchurInput n μK)
    (v : BinaryForm n) (f : ℍ → BinaryForm n)
    (hHaar : CoefficientHaarInput n μG μK v f) :
    (∫ g, ‖liftedCoefficient n v f g‖^2 ∂μG) =
      (‖v‖^2 / ((n+1:ℝ)*weightConstant n)) * ∫ q in Ball, ballDensity n q * ‖f q‖^2 := by
  rw [hHaar, ← integral_const_mul]
  apply setIntegral_congr_fun ball_isOpen.measurableSet
  intro q hq
  dsimp only
  simp_rw [fullLift_section_compact n f q hq]
  rw [hSchur, weightedSpinor, norm_smul, Real.norm_eq_abs,
    abs_of_pos (ballWeight_pos _ hq), mul_pow]
  have hw := lift_weight_cancellation n hn q hq
  have hc := (weightConstant_pos n hn).ne'
  calc
    _ = ((ballScale q)⁻¹ ^ 4 * (ballWeight (((n:ℝ)+2)/2) q)^2) * ‖f q‖^2 * ‖v‖^2 / (n+1:ℝ) := by ring
    _ = _ := by rw [hw]; unfold ballDensity; field_simp

/-- mathlib's L² norm, stated directly as the square-norm integral. -/
theorem l2_norm_sq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] {μ : Measure X} (f : Lp E 2 μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def (𝕜 := ℂ), ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  simp only [inner_self_eq_norm_sq_to_K]
  apply integral_congr_ae
  filter_upwards [] with x
  change ((‖f x‖ : ℂ)^2).re = ‖f x‖^2
  simp [pow_two]

/-- The polynomial weighted L² norm uses exactly C_n s^(n-2) dv. -/
theorem ballL2_norm_sq_integral (n : ℕ) (hn : 2 ≤ n) (f : BallL2 n) :
    ‖f‖^2 = ∫ q in Ball, ballDensity n q * ‖f q‖^2 := by
  calc
    _ = ∫ q, ‖f q‖^2 ∂weightedBallMeasure n := l2_norm_sq_integral f
    _ = _ := ?_
  change (∫ q, ‖f q‖^2 ∂(volume.restrict Ball).withDensity (fun q => ENNReal.ofReal (ballDensity n q))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
      (continuous_ballDensity n).measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply setIntegral_congr_fun ball_isOpen.measurableSet
  intro q hq
  simp [ENNReal.toReal_ofReal (ballDensity_pos n hn hq).le]

section ClosedImage
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace X] (μ : Measure X)

/-- Any positive squared-norm constant yields a scaled linear isometry. -/
def normalizedCoefficientEmbedding (W : H →ₗ[ℂ] Lp ℂ 2 μ) (a : ℝ) (ha : 0 < a)
    (hW : ∀ f, ‖W f‖^2 = a * ‖f‖^2) : H →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toLinearMap := (Real.sqrt a)⁻¹ • W
  norm_map' f := by
    simp only [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Real.sqrt_nonneg a)]
    have h : ‖W f‖ = Real.sqrt a * ‖f‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg _))).mp
      rw [mul_pow, Real.sq_sqrt ha.le, hW]
    rw [h, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_mul]

/-- The closed-image step of DS4, for an actual L²-valued linear map. -/
theorem coefficientEmbedding_closed_range (W : H →ₗ[ℂ] Lp ℂ 2 μ)
    (a : ℝ) (ha : 0 < a) (hW : ∀ f, ‖W f‖^2 = a * ‖f‖^2) :
    Function.Injective W ∧ IsClosed (Set.range W) := by
  let e := normalizedCoefficientEmbedding μ W a ha hW
  have he : IsClosed (Set.range e) := e.isometry.isClosedEmbedding.isClosed_range
  have hr : Set.range e = Set.range W := by
    ext y
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨(Real.sqrt a)⁻¹ • f, by simp [e, normalizedCoefficientEmbedding]⟩
    · rintro ⟨f, rfl⟩
      refine ⟨Real.sqrt a • f, ?_⟩
      simp [e, normalizedCoefficientEmbedding, smul_smul, (Real.sqrt_pos.mpr ha).ne']
  refine ⟨?_, hr ▸ he⟩
  intro f g hfg
  apply e.injective
  change (Real.sqrt a)⁻¹ • W f = (Real.sqrt a)⁻¹ • W g
  rw [hfg]
end ClosedImage

/-- Combining the concrete integral calculation with an L² realization gives the
norm and closed-image conclusions. The realization and its coefficient formula
are explicit local bridge hypotheses, not consequences asserted in this file. -/
theorem DS4_closed_embedding_of_inputs
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (n : ℕ) (hn : 2 ≤ n) (μG : Measure Sp11) (μK : Measure CompactPair)
    (hSchur : CompactSchurInput n μK) (v : BinaryForm n) (hv : v ≠ 0)
    (representative : H → ℍ → BinaryForm n)
    (hNorm : ∀ f, ‖f‖^2 = ∫ q in Ball, ballDensity n q * ‖representative f q‖^2)
    (hHaar : ∀ f, CoefficientHaarInput n μG μK v (representative f))
    (W : H →ₗ[ℂ] Lp ℂ 2 μG)
    (hW : ∀ f, (W f : Sp11 → ℂ) =ᵐ[μG] liftedCoefficient n v (representative f)) :
    (∀ f, ‖W f‖^2 = (‖v‖^2 / ((n+1:ℝ)*weightConstant n)) * ‖f‖^2) ∧
      Function.Injective W ∧ IsClosed (Set.range W) := by
  have he (f : H) : ‖W f‖^2 = (‖v‖^2 / ((n+1:ℝ)*weightConstant n)) * ‖f‖^2 := by
    rw [l2_norm_sq_integral]
    calc
      _ = ∫ g, ‖liftedCoefficient n v (representative f) g‖^2 ∂μG :=
        integral_congr_ae ((hW f).fun_comp fun z => ‖z‖^2)
      _ = _ := by rw [DS4_coefficient_integral_of_haar_schur n hn μG μK hSchur v _ (hHaar f), ← hNorm f]
  refine ⟨he, coefficientEmbedding_closed_range μG W _ ?_ he⟩
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (mul_pos (by positivity) (weightConstant_pos n hn))

end MathResearch.Spinor
