module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

/-!
Infrastructure checks only. These declarations are not formalizations of wiki claims.
They exercise mathlib imports, the ring tactic, and a finite-sum library theorem.
-/

public section

open scoped BigOperators

namespace MathResearch.SmokeTest

theorem square_expansion (x y : ℚ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

theorem sum_add {ι : Type*} (s : Finset ι) (f g : ι → ℚ) :
    (∑ i ∈ s, (f i + g i)) = (∑ i ∈ s, f i) + ∑ i ∈ s, g i := by
  exact Finset.sum_add_distrib

end MathResearch.SmokeTest
