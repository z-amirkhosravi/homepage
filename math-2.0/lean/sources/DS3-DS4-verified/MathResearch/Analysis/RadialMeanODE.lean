module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! The regular radial harmonic ODE in dimension four. Multiplication by r³
removes the first-derivative coefficient; regularity at the center removes the
singular solution. This lemma is independent of quaternionic research. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace MathResearch.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A twice differentiable regular solution of r M'' + 3 M' = 0 is constant. -/
theorem radialMeanODE_constant {M M' M'' : ℝ → E}
    (h1 : ∀ t ∈ Ico (0:ℝ) 1, HasDerivAt M (M' t) t)
    (h2 : ∀ t ∈ Ico (0:ℝ) 1, HasDerivAt M' (M'' t) t)
    (h0 : M' 0 = 0)
    (hODE : ∀ t ∈ Ioo (0:ℝ) 1, t • M'' t + (3:ℝ) • M' t = 0)
    {r : ℝ} (hr : r ∈ Ico (0:ℝ) 1) : M r = M 0 := by
  have hg (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      HasDerivAt (fun x => x^3 • M' x) 0 t := by
    have h := ((hasDerivAt_id t).pow 3).smul (h2 t ht)
    by_cases hz : t = 0
    · simpa [hz] using! h
    · have he := congrArg (fun v : E => t^2 • v) (hODE t ⟨lt_of_le_of_ne ht.1 (Ne.symm hz), ht.2⟩)
      simp only [smul_add, smul_smul, smul_zero] at he
      convert! h using 1
      calc
        0 = (t^2*t) • M'' t + (t^2*3) • M' t := he.symm
        _ = _ := by
          simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
          module
  have hd0 (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : M' t = 0 := by
    by_cases hz : t = 0
    · simpa [hz] using! h0
    have H := constant_of_has_deriv_right_zero
      (f := fun x => x^3 • M' x) (a := 0) (b := t)
      (fun x hx => (hg x ⟨hx.1, hx.2.trans_lt ht.2⟩).continuousAt.continuousWithinAt)
      (fun x hx => (hg x ⟨hx.1, hx.2.trans ht.2⟩).hasDerivWithinAt)
      t (right_mem_Icc.mpr ht.1)
    simp only [zero_pow (by decide : 3 ≠ 0), zero_smul] at H
    exact (smul_eq_zero.mp H).resolve_left (pow_ne_zero 3 hz)
  exact constant_of_has_deriv_right_zero
    (fun x hx => (h1 x ⟨hx.1, hx.2.trans_lt hr.2⟩).continuousAt.continuousWithinAt)
    (fun x hx => by simpa only [hd0 x ⟨hx.1, hx.2.trans hr.2⟩] using
      (h1 x ⟨hx.1, hx.2.trans hr.2⟩).hasDerivWithinAt (s := Ici x))
    r (right_mem_Icc.mpr hr.1)

end MathResearch.Analysis
