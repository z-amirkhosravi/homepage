module
public import MathResearch.Fueter.KernelNumerator
public import MathResearch.Fueter.RealMellin

/-! TH1: the absolutely convergent Mellin formula for real components of EI1's numerators. -/
@[expose] public section
noncomputable section
open scoped Quaternion Topology BigOperators ContDiff
open MeasureTheory Set Real
namespace MathResearch.Fueter

@[simp] theorem kernelNumerator_eval_zero (ν : Fin 3 → ℕ) (k : Fin 4) :
    polyEval (kernelNumerator ν k) 0 = 0 := by
  unfold kernelNumerator
  cases spatialDerivativeList ν with
  | nil => simp [numeratorJet]
  | cons j l => simp [numeratorJet, numeratorStep, polyEval_sub, polyEval_mul]

variable (L : Submodule ℤ ℍ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- TH1's scalar Eisenstein coefficient, expressed directly as a polynomial lattice sum. -/
def numeratorCoefficient (ν : Fin 3 → ℕ) (k : Fin 4) : ℝ :=
  ∑' l : {l : L // l ≠ 0},
    polyEval (kernelNumerator ν k) (l.1 : ℍ) /
      Quaternion.normSq (l.1 : ℍ) ^ ((∑ i, ν i) + 2)

/-- The imaginary-axis theta series `θ_{L,H}(it)`, including the zero lattice point. -/
def harmonicTheta (ν : Fin 3 → ℕ) (k : Fin 4) (t : ℝ) : ℝ :=
  ∑' l : L, polyEval (kernelNumerator ν k) (l : ℍ) * exp (-Real.pi * t * Quaternion.normSq (l : ℍ))

theorem summable_numeratorCoefficient_norm (ν : Fin 3 → ℕ) (k : Fin 4)
    (hν : 2 ≤ ∑ i, ν i) :
    Summable (fun l : {l : L // l ≠ 0} =>
      |polyEval (kernelNumerator ν k) (l.1 : ℍ)| /
        Quaternion.normSq (l.1 : ℍ) ^ ((∑ i, ν i) + 2)) := by
  have hc : Summable (fun l : {l : L // l ≠ 0} => ‖realCoord k (higherKernel ν (l.1 : ℍ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => (realCoord k).le_opNorm _)
      ((summable_norm_eisenstein L ν hν).mul_left ‖realCoord k‖)
  convert hc using 1
  funext l
  have hn : 0 ≤ Quaternion.normSq (l.1 : ℍ) := Quaternion.normSq_nonneg
  rw [kernelNumerator_represents ν k (by simpa using l.2), Real.norm_eq_abs, abs_div,
    abs_of_nonneg (pow_nonneg hn _)]

/-- The new scalar coefficient is precisely a real component of the existing coefficient. -/
theorem numeratorCoefficient_eq_component (ν : Fin 3 → ℕ) (k : Fin 4)
    (hν : 2 ≤ ∑ i, ν i) : numeratorCoefficient L ν k = realCoord k (eisensteinCoefficient L ν) := by
  rw [numeratorCoefficient, eisensteinCoefficient,
    (realCoord k).map_tsum (summable_norm_eisenstein L ν hν).of_norm]
  apply tsum_congr
  intro l
  exact (kernelNumerator_represents ν k (by simpa using l.2)).symm

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem harmonicTheta_eq_nonzero (ν : Fin 3 → ℕ) (k : Fin 4) (t : ℝ) :
    harmonicTheta L ν k t = ∑' l : {l : L // l ≠ 0},
      polyEval (kernelNumerator ν k) (l.1 : ℍ) * exp (-Real.pi * t * Quaternion.normSq (l.1 : ℍ)) := by
  unfold harmonicTheta
  symm
  apply tsum_subtype_eq_of_support_subset (s := {l : L | l ≠ 0})
    (f := fun l : L => polyEval (kernelNumerator ν k) (l : ℍ) *
      exp (-Real.pi * t * Quaternion.normSq (l : ℍ)))
  intro l hl
  by_contra h
  have : l = 0 := by simpa using h
  subst l
  simp [Function.mem_support] at hl

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- The positive rates appearing in the real Mellin lemmas. -/
private theorem theta_rate_pos (l : {l : L // l ≠ 0}) :
    0 < Real.pi * Quaternion.normSq (l.1 : ℍ) := by
  exact mul_pos Real.pi_pos (lt_of_le_of_ne Quaternion.normSq_nonneg
    (Ne.symm (Quaternion.normSq_ne_zero.mpr (by simpa using l.2))))

private theorem summable_theta_rate (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i) :
    Summable (fun l : {l : L // l ≠ 0} =>
      |polyEval (kernelNumerator ν k) (l.1 : ℍ)| /
        (Real.pi * Quaternion.normSq (l.1 : ℍ)) ^ ((∑ i, ν i) + 2)) := by
  simpa only [mul_pow, div_mul_eq_div_div, div_right_comm] using
    (summable_numeratorCoefficient_norm L ν k hν).div_const (Real.pi ^ ((∑ i, ν i) + 2))

theorem summable_harmonicTheta (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun l : L => polyEval (kernelNumerator ν k) (l : ℍ) *
      exp (-Real.pi * t * Quaternion.normSq (l : ℍ))) := by
  have hs := summable_exp_series ((∑ i, ν i) + 2) (theta_rate_pos L)
    (summable_theta_rate L ν k hν) ht
  have he (l : L) : -(Real.pi * Quaternion.normSq (l : ℍ)) * t =
      -Real.pi * t * Quaternion.normSq (l : ℍ) := by ring
  simp_rw [he] at hs
  have hh := (Set.finite_singleton (0 : L)).summable_compl_iff
    (f := fun l : L => polyEval (kernelNumerator ν k) (l : ℍ) *
      exp (-Real.pi * t * Quaternion.normSq (l : ℍ)))
  apply hh.mp
  change Summable (fun l : {l : L // l ≠ 0} =>
    polyEval (kernelNumerator ν k) (l.1 : ℍ) * exp (-Real.pi * t * Quaternion.normSq (l.1 : ℍ)))
  exact hs

/-- Absolute convergence of precisely the sum of weighted integrals in TH1. -/
theorem harmonicTheta_absolute_interchange (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i) :
    Summable (fun l : {l : L // l ≠ 0} => ∫ t : ℝ in Ioi 0,
      ‖t ^ ((∑ i, ν i) + 1) * (polyEval (kernelNumerator ν k) (l.1 : ℍ) *
        exp (-Real.pi * t * Quaternion.normSq (l.1 : ℍ)))‖) := by
  have hs := summable_integral_norm_mellin ((∑ i, ν i) + 1) (theta_rate_pos L)
    (by simpa [Nat.add_assoc] using summable_theta_rate L ν k hν)
  have he (l : {l : L // l ≠ 0}) (t : ℝ) :
      -(Real.pi * Quaternion.normSq (l.1 : ℍ)) * t =
      -Real.pi * t * Quaternion.normSq (l.1 : ℍ) := by ring
  simpa only [Nat.add_assoc, he] using hs

theorem harmonicTheta_integrable (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i) :
    IntegrableOn (fun t : ℝ => t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t) (Ioi 0) := by
  have hi := integrableOn_mellin_series ((∑ i, ν i) + 1) (theta_rate_pos L)
    (by simpa [Nat.add_assoc] using summable_theta_rate L ν k hν)
  convert hi using 1
  funext t
  rw [harmonicTheta_eq_nonzero]
  congr 1
  apply tsum_congr
  intro l
  congr 2
  ring

/-- TH1's Mellin value, in fact valid for every spatial order at least two. -/
theorem harmonicTheta_mellin (ν : Fin 3 → ℕ) (k : Fin 4) (hν : 2 ≤ ∑ i, ν i) :
    numeratorCoefficient L ν k =
      Real.pi ^ ((∑ i, ν i) + 2) / Gamma (((∑ i, ν i) : ℕ) + 2) *
        ∫ t : ℝ in Ioi 0, t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t := by
  have he := real_mellin_series ((∑ i, ν i) + 1) (theta_rate_pos L)
    (by simpa [Nat.add_assoc] using summable_theta_rate L ν k hν)
  have hfun (t : ℝ) : (∑' l : {l : L // l ≠ 0},
      polyEval (kernelNumerator ν k) (l.1 : ℍ) * exp (-(Real.pi * Quaternion.normSq (l.1 : ℍ)) * t)) =
      harmonicTheta L ν k t := by
    rw [harmonicTheta_eq_nonzero]
    apply tsum_congr
    intro l
    congr 2
    ring
  simp_rw [hfun, Nat.add_assoc, Nat.cast_add, Nat.cast_one] at he
  have hcoeff : (∑' l : {l : L // l ≠ 0},
      polyEval (kernelNumerator ν k) (l.1 : ℍ) /
        (Real.pi * Quaternion.normSq (l.1 : ℍ)) ^ ((∑ i, ν i) + 2)) =
      numeratorCoefficient L ν k / Real.pi ^ ((∑ i, ν i) + 2) := by
    rw [numeratorCoefficient, ← tsum_div_const]
    apply tsum_congr
    intro l
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  norm_num only [Nat.reduceAdd, one_add_one_eq_two] at he
  simp only [add_assoc, one_add_one_eq_two] at he
  rw [hcoeff] at he
  rw [he]
  have hg : Gamma (((∑ i, ν i) : ℕ) + 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  field_simp

/-- TH1/v1: the stated odd-order Mellin identity, with all convergence claims proved. -/
theorem TH1_v1 (ν : Fin 3 → ℕ) (k : Fin 4) (_hodd : Odd (∑ i, ν i))
    (hν : 3 ≤ ∑ i, ν i) :
    (∀ t : ℝ, 0 < t → Summable (fun l : L =>
      polyEval (kernelNumerator ν k) (l : ℍ) * exp (-Real.pi * t * Quaternion.normSq (l : ℍ)))) ∧
    Summable (fun l : {l : L // l ≠ 0} => |polyEval (kernelNumerator ν k) (l.1 : ℍ)| /
      Quaternion.normSq (l.1 : ℍ) ^ ((∑ i, ν i) + 2)) ∧
    Summable (fun l : {l : L // l ≠ 0} => ∫ t : ℝ in Ioi 0,
      ‖t ^ ((∑ i, ν i) + 1) * (polyEval (kernelNumerator ν k) (l.1 : ℍ) *
        exp (-Real.pi * t * Quaternion.normSq (l.1 : ℍ)))‖) ∧
    IntegrableOn (fun t : ℝ => t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t) (Ioi 0) ∧
    numeratorCoefficient L ν k = realCoord k (eisensteinCoefficient L ν) ∧
    numeratorCoefficient L ν k = Real.pi ^ ((∑ i, ν i) + 2) / Gamma (((∑ i, ν i) : ℕ) + 2) *
      ∫ t : ℝ in Ioi 0, t ^ ((∑ i, ν i) + 1) * harmonicTheta L ν k t := by
  have h₂ : 2 ≤ ∑ i, ν i := by omega
  exact ⟨fun _ ht => summable_harmonicTheta L ν k h₂ ht,
    summable_numeratorCoefficient_norm L ν k h₂, harmonicTheta_absolute_interchange L ν k h₂,
    harmonicTheta_integrable L ν k h₂, numeratorCoefficient_eq_component L ν k h₂,
    harmonicTheta_mellin L ν k h₂⟩

end MathResearch.Fueter
