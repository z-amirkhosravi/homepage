module
public import MathResearch.Spinor.CompactIrreducible
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Group.Integral

/-! Compact Schur orthogonality for the actual quaternionic polynomial action.
The proof averages rank-one operators, applies irreducibility, and computes trace. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Quaternion BigOperators
open MeasureTheory InnerProductSpace ContinuousLinearMap
namespace MathResearch.Spinor

def compactPolynomialUnitary (n : ℕ) (a : Fueter.UnitQuaternion) :
    BinaryForm n ≃ₗᵢ[ℂ] BinaryForm n :=
  { LinearEquiv.ofBijective (unitQuaternionPolynomialRepresentation n a)
      ((unitQuaternionPolynomialRepresentation n).apply_bijective a) with
    norm_map' := unitQuaternionAction_norm n a (Fueter.unitQuaternion_normSq a) }

@[simp] theorem compactPolynomialUnitary_apply (n : ℕ) (a : Fueter.UnitQuaternion) (p : BinaryForm n) :
    compactPolynomialUnitary n a p = polynomialRepresentation n (quaternionMatrix a) p := rfl

theorem continuous_compactPolynomialOrbit (n : ℕ) (v : BinaryForm n) :
    Continuous (fun a : Fueter.UnitQuaternion => compactPolynomialUnitary n a v) := by
  change Continuous (fun a : Fueter.UnitQuaternion => polynomialRepresentation n (quaternionMatrix a) v)
  simpa only [Function.comp_def] using!
    ((contDiff_quaternionPolynomialRepresentation n).continuous.comp
      (continuous_subtype_val.prodMk (continuous_const (y := v))))

theorem compactPolynomialUnitary_mul (n : ℕ) (a b : Fueter.UnitQuaternion) (v : BinaryForm n) :
    compactPolynomialUnitary n (a*b) v = compactPolynomialUnitary n a (compactPolynomialUnitary n b v) :=
  (unitQuaternionPolynomialRepresentation n).map_mul a b |> congrArg (fun L => L v)

/-- Schur's scalar-commutant conclusion, proved for this representation. -/
theorem compactPolynomial_commutant_scalar (m : ℕ) (T : Module.End ℂ (BinaryForm (m+1)))
    (hT : ∀ a : Fueter.UnitQuaternion, ∀ v,
      T (compactPolynomialUnitary (m+1) a v) = compactPolynomialUnitary (m+1) a (T v)) :
    ∃ z : ℂ, T = z • LinearMap.id := by
  let : Nontrivial (BinaryForm (m+1)) := (coefficientEquiv (m+1)).symm.injective.nontrivial
  obtain ⟨z, hz⟩ := T.exists_eigenvalue
  have hinv : CompactPolynomialInvariant (m+1) (T.eigenspace z) := by
    intro a p hp
    rw [Module.End.mem_eigenspace_iff] at hp ⊢
    change T (compactPolynomialUnitary (m+1) a p) = z • compactPolynomialUnitary (m+1) a p
    rw [hT, hp, map_smul]
  have ht : T.eigenspace z = ⊤ :=
    (compactPolynomial_irreducible m _ hinv).resolve_left hz
  refine ⟨z, ?_⟩
  apply LinearMap.ext
  intro p
  exact Module.End.mem_eigenspace_iff.mp (ht ▸ Submodule.mem_top : p ∈ T.eigenspace z)

/-- Average of the orbit of a positive rank-one operator. -/
def compactRankOneAverage (n : ℕ) (v : BinaryForm n) : BinaryForm n →L[ℂ] BinaryForm n :=
  ∫ a, rankOne ℂ (compactPolynomialUnitary n a v) (compactPolynomialUnitary n a v) ∂unitQuaternionHaar

theorem compactRankOneOrbit_continuous (n : ℕ) (v : BinaryForm n) :
    Continuous (fun a : Fueter.UnitQuaternion =>
      rankOne ℂ (compactPolynomialUnitary n a v) (compactPolynomialUnitary n a v)) := by
  simp_rw [rankOne_def]
  exact ((smulRightL ℂ (BinaryForm n) (BinaryForm n)).continuous.comp
    ((innerSL ℂ).continuous.comp (continuous_compactPolynomialOrbit n v))).clm_apply
    (continuous_compactPolynomialOrbit n v)

theorem compactRankOneOrbit_integrable (n : ℕ) (v : BinaryForm n) :
    Integrable (fun a : Fueter.UnitQuaternion =>
      rankOne ℂ (compactPolynomialUnitary n a v) (compactPolynomialUnitary n a v)) unitQuaternionHaar :=
  (compactRankOneOrbit_continuous n v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem compactRankOneAverage_apply (n : ℕ) (v x : BinaryForm n) :
    compactRankOneAverage n v x =
      ∫ a, inner ℂ (compactPolynomialUnitary n a v) x • compactPolynomialUnitary n a v ∂unitQuaternionHaar :=
  integral_apply (compactRankOneOrbit_integrable n v) x

theorem compactRankOneAverage_commutes (n : ℕ) (v : BinaryForm n)
    (b : Fueter.UnitQuaternion) (x : BinaryForm n) :
    compactRankOneAverage n v (compactPolynomialUnitary n b x) =
      compactPolynomialUnitary n b (compactRankOneAverage n v x) := by
  rw [compactRankOneAverage_apply, compactRankOneAverage_apply]
  change _ = (compactPolynomialUnitary n b).toLinearIsometry (∫ a,
    inner ℂ (compactPolynomialUnitary n a v) x • compactPolynomialUnitary n a v ∂unitQuaternionHaar)
  rw [← (compactPolynomialUnitary n b).toLinearIsometry.integral_comp_comm]
  rw [← integral_mul_left_eq_self (fun a : Fueter.UnitQuaternion =>
    inner ℂ (compactPolynomialUnitary n a v) (compactPolynomialUnitary n b x) •
      compactPolynomialUnitary n a v) b]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [compactPolynomialUnitary_mul, (compactPolynomialUnitary n b).inner_map_map, map_smul]
  rfl

def polynomialTraceCLM (n : ℕ) : (BinaryForm n →L[ℂ] BinaryForm n) →L[ℂ] ℂ :=
  ((LinearMap.trace ℂ (BinaryForm n)).comp (ContinuousLinearMap.coeLM ℂ)).toContinuousLinearMap

theorem compactRankOneAverage_trace (n : ℕ) (v : BinaryForm n) :
    polynomialTraceCLM n (compactRankOneAverage n v) = (‖v‖:ℂ)^2 := by
  rw [compactRankOneAverage, ← (polynomialTraceCLM n).integral_comp_comm
    (compactRankOneOrbit_integrable n v)]
  have he (a : Fueter.UnitQuaternion) : polynomialTraceCLM n
      (rankOne ℂ (compactPolynomialUnitary n a v) (compactPolynomialUnitary n a v)) = (‖v‖:ℂ)^2 := by
    change LinearMap.trace ℂ (BinaryForm n) (rankOne ℂ _ _).toLinearMap = _
    rw [trace_rankOne, inner_self_eq_norm_sq_to_K, (compactPolynomialUnitary n a).norm_map]
    rfl
  simp_rw [he]
  simp

/-- The averaged rank-one operator is the scalar predicted by its trace. -/
theorem compactRankOneAverage_eq (m : ℕ) (v : BinaryForm (m+1)) :
    compactRankOneAverage (m+1) v =
      ((‖v‖:ℂ)^2 / (m+2:ℂ)) • ContinuousLinearMap.id ℂ (BinaryForm (m+1)) := by
  obtain ⟨z, hz⟩ := compactPolynomial_commutant_scalar m
    (compactRankOneAverage (m+1) v).toLinearMap (compactRankOneAverage_commutes (m+1) v)
  have ht := compactRankOneAverage_trace (m+1) v
  change LinearMap.trace ℂ (BinaryForm (m+1)) (compactRankOneAverage (m+1) v).toLinearMap = _ at ht
  rw [hz, map_smul, LinearMap.trace_id, finrank_binaryForm] at ht
  have hd : (m+2:ℂ) ≠ 0 := by exact_mod_cast (show m+2 ≠ 0 by omega)
  have hz' : z = (‖v‖:ℂ)^2 / (m+2:ℂ) := by
    apply (eq_div_iff hd).mpr
    convert ht using 1
    push_cast
    ring
  apply ContinuousLinearMap.coe_injective
  rw [hz, hz']
  rfl

theorem compactPolynomial_schur (m : ℕ) (u v : BinaryForm (m+1)) :
    (∫ a, ‖inner ℂ (compactPolynomialUnitary (m+1) a v) u‖^2 ∂unitQuaternionHaar) =
      ‖u‖^2 * ‖v‖^2 / (m+2:ℝ) := by
  have hi := (ContinuousLinearMap.apply ℂ (BinaryForm (m+1)) u).integrable_comp
    (compactRankOneOrbit_integrable (m+1) v)
  change Integrable (fun a => inner ℂ (compactPolynomialUnitary (m+1) a v) u •
    compactPolynomialUnitary (m+1) a v) unitQuaternionHaar at hi
  have he := congrArg (fun T : BinaryForm (m+1) →L[ℂ] BinaryForm (m+1) => inner ℂ u (T u))
    (compactRankOneAverage_eq m v)
  rw [compactRankOneAverage_apply, ← integral_inner hi] at he
  have hp (a : Fueter.UnitQuaternion) :
      inner ℂ u (inner ℂ (compactPolynomialUnitary (m+1) a v) u • compactPolynomialUnitary (m+1) a v) =
        ((‖inner ℂ (compactPolynomialUnitary (m+1) a v) u‖^2 : ℝ) : ℂ) := by
    rw [inner_smul_right, ← inner_conj_symm u (compactPolynomialUnitary (m+1) a v)]
    rw [mul_comm, Complex.conj_mul', Complex.ofReal_pow]
  simp_rw [hp] at he
  apply Complex.ofReal_injective
  calc
    _ = ∫ a, ((‖inner ℂ (compactPolynomialUnitary (m+1) a v) u‖^2 : ℝ):ℂ) ∂unitQuaternionHaar := by
      exact integral_complex_ofReal.symm
    _ = _ := he
    _ = _ := by
      simp [inner_smul_right, inner_self_eq_norm_sq_to_K]
      ring

theorem compactPolynomial_inverse_inner (n : ℕ) (a : Fueter.UnitQuaternion) (u v : BinaryForm n) :
    inner ℂ v (polynomialRepresentation n (quaternionMatrix ((a:ℍ)⁻¹)) u) =
      inner ℂ (compactPolynomialUnitary n a v) u := by
  have hi : ((a⁻¹ : Fueter.UnitQuaternion) : ℍ) = (a:ℍ)⁻¹ := by
    rw [Quaternion.inv_def, Fueter.unitQuaternion_normSq]
    simp
  have h := (compactPolynomialUnitary n a).inner_map_map v (compactPolynomialUnitary n a⁻¹ u)
  rw [← compactPolynomialUnitary_mul, mul_inv_cancel] at h
  have h1 : compactPolynomialUnitary n 1 u = u :=
    (unitQuaternionPolynomialRepresentation n).map_one |> congrArg (fun L => L u)
  rw [h1] at h
  simpa only [compactPolynomialUnitary_apply, hi] using h.symm

/-- The precise compact Schur input in the internal DS4 norm calculation. -/
theorem compactSchurInput_proved (m : ℕ) : CompactSchurInput (m+1) compactHaar := by
  intro u v
  simp_rw [compactPolynomial_inverse_inner]
  change (∫ k : Fueter.UnitQuaternion × Fueter.UnitQuaternion,
    ‖inner ℂ (compactPolynomialUnitary (m+1) k.2 v) u‖^2 ∂unitQuaternionHaar.prod unitQuaternionHaar) = _
  have h := integral_fun_snd (μ := unitQuaternionHaar) (ν := unitQuaternionHaar)
    (fun a => ‖inner ℂ (compactPolynomialUnitary (m+1) a v) u‖^2)
  calc
    _ = ∫ a, ‖inner ℂ (compactPolynomialUnitary (m+1) a v) u‖^2 ∂unitQuaternionHaar := by
      simpa using! h
    _ = _ := by convert compactPolynomial_schur m u v using 1; push_cast; ring

end MathResearch.Spinor
