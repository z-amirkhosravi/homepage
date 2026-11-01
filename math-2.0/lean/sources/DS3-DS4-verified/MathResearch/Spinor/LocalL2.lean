module
public import MathResearch.Spinor.WeightedLocalization

/-! The compact-subset L² estimate used in the written proof of DS2. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal Topology
open MeasureTheory
namespace MathResearch.Spinor

/-- The positive weight has a positive lower bound on every nonempty compact subset of B. -/
theorem ballDensity_compact_lower_bound (n : ℕ) (hn : 2 ≤ n) {K : Set ℍ}
    (hK : IsCompact K) (hKB : K ⊆ Ball) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ K, a ≤ ballDensity n q := by
  by_cases he : K.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn he (continuous_ballDensity n).continuousOn
    exact ⟨ballDensity n q, ballDensity_pos n hn (hKB hq), hmin⟩
  · exact ⟨1, zero_lt_one, fun q hq => (he ⟨q, hq⟩).elim⟩

theorem compact_volume_le_weighted (n : ℕ) (hn : 2 ≤ n) {K : Set ℍ}
    (hK : IsCompact K) (hKB : K ⊆ Ball) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ volume.restrict K ≤ c • weightedBallMeasure n := by
  classical
  obtain ⟨a, ha, hbound⟩ := ballDensity_compact_lower_bound n hn hK hKB
  refine ⟨ENNReal.ofReal a⁻¹, ENNReal.ofReal_ne_top, ?_⟩
  have hi : (volume.restrict Ball).withDensity (K.indicator (fun _ => (1 : ℝ≥0∞))) =
      volume.restrict K := by
    rw [withDensity_indicator hK.measurableSet]
    change ((volume.restrict Ball).restrict K).withDensity 1 = _
    rw [withDensity_one, Measure.restrict_restrict hK.measurableSet,
      Set.inter_eq_left.mpr hKB]
  rw [← hi, weightedBallMeasure, ← withDensity_smul _
    (continuous_ballDensity n).measurable.ennreal_ofReal]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem ball_isOpen.measurableSet] with q hq
  by_cases hk : q ∈ K
  · simp only [Set.indicator_of_mem hk, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    exact ENNReal.one_le_ofReal.mpr ((le_inv_mul_iff₀ ha).mpr (by simpa using hbound q hk))
  · simp [Set.indicator_of_notMem hk]

/-- Restrict the actual weighted L² class to ordinary Lebesgue L² on a compact subset.
Mathlib supplies the continuous map from the proved measure bound. -/
def compactL2Restriction (n : ℕ) (hn : 2 ≤ n) {K : Set ℍ}
    (hK : IsCompact K) (hKB : K ⊆ Ball) :
    BallL2 n →L[ℝ] Lp (BinaryForm n) 2 (volume.restrict K) :=
  Lp.LpToLpOfMeasureLeSMul (compact_volume_le_weighted n hn hK hKB).choose_spec.1
    (compact_volume_le_weighted n hn hK hKB).choose_spec.2

theorem compactL2Restriction_ae (n : ℕ) (hn : 2 ≤ n) {K : Set ℍ}
    (hK : IsCompact K) (hKB : K ⊆ Ball) (f : BallL2 n) :
    (compactL2Restriction n hn hK hKB f : ℍ → BinaryForm n) =ᵐ[volume.restrict K] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- Exactly the local convergence assertion in DS2: weighted L² convergence
implies ordinary L² convergence on every compact subset of the open ball. -/
theorem weightedL2_tendsto_locally {ι : Type*} {l : Filter ι} (n : ℕ) (hn : 2 ≤ n)
    {K : Set ℍ} (hK : IsCompact K) (hKB : K ⊆ Ball)
    {f : ι → BallL2 n} {g : BallL2 n} (hf : Filter.Tendsto f l (𝓝 g)) :
    Filter.Tendsto (fun i => compactL2Restriction n hn hK hKB (f i)) l
      (𝓝 (compactL2Restriction n hn hK hKB g)) :=
  ((compactL2Restriction n hn hK hKB).continuous.tendsto g).comp hf

end MathResearch.Spinor
