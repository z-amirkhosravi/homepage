/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The compact approximation proof below adapts mathlib's ContinuousMapDense
argument, adding support strictly inside the open ball.
-/
module
public import MathResearch.Spinor.L2StrongContinuity

/-! Density of continuous functions whose compact support lies strictly inside B.
The proof specializes mathlib's simple-function approximation and Urysohn argument
to a measure carried by B; it does not use bounded-continuous density. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Quaternion ENNReal NNReal Topology
open MeasureTheory Set Filter
namespace MathResearch.Spinor

theorem ae_mem_ball (n : ℕ) (hn : 2 ≤ n) : ∀ᵐ q ∂weightedBallMeasure n, q ∈ Ball :=
  (ae_weightedBall_iff n hn _).mpr (ae_restrict_mem ball_isOpen.measurableSet)

theorem exists_compactContinuous_ball_approx (n : ℕ) (hn : 2 ≤ n)
    {f : ℍ → BinaryForm n} (hf : MemLp f 2 (weightedBallMeasure n))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ F : ℍ → BinaryForm n, eLpNorm (f-F) 2 (weightedBallMeasure n) ≤ ε ∧
      Continuous F ∧ MemLp F 2 (weightedBallMeasure n) ∧
      HasCompactSupport F ∧ tsupport F ⊆ Ball := by
  let μ := weightedBallMeasure n
  apply hf.induction_dense (by norm_num) _ _ _ hε
  · intro c t ht htμ ε hε
    obtain ⟨δ, hδ, hhalf⟩ := exists_Lp_half (BinaryForm n) μ 2 hε
    obtain ⟨η, hη, hsmall⟩ : ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set ℍ,
        μ s ≤ η → NullMeasurableSet s μ → eLpNorm (s.indicator fun _ => c) 2 μ ≤ δ :=
      exists_eLpNorm_indicator_le (p := 2) (μ := μ) (by norm_num) c hδ.ne'
    obtain ⟨s, hst, hsc, hclosed, hdiff⟩ :=
      (ht.inter ball_isOpen.measurableSet).exists_isCompact_isClosed_sdiff_lt
        ((measure_mono inter_subset_left).trans_lt htμ).ne
        (show (η : ℝ≥0∞) ≠ 0 by exact_mod_cast hη.ne')
    have hsB : s ⊆ Ball := hst.trans inter_subset_right
    have hst' : s ⊆ t := hst.trans inter_subset_left
    have hdiff' : μ (t \ s) < η := by
      have he : t \ s =ᵐ[μ] (t ∩ Ball) \ s := by
        filter_upwards [ae_mem_ball n hn] with q hq
        simp [hq]
      rw [measure_congr he]
      exact hdiff
    have hI : eLpNorm ((s.indicator fun _ => c) - t.indicator (fun _ => c)) 2 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hst']
      exact hsmall _ hdiff'.le (ht.diff hclosed.measurableSet).nullMeasurableSet
    obtain ⟨v, hv, hsv, hvB⟩ := hsc.exists_isOpen_closure_subset (ball_isOpen.mem_nhdsSet.mpr hsB)
    obtain ⟨k, hk, hsk⟩ := exists_compact_superset hsc
    obtain ⟨F, hF, hclose, hbound, hsupp, hmem⟩ :=
      exists_continuous_eLpNorm_sub_le_of_closed (by norm_num : (2:ℝ≥0∞) ≠ ∞)
        hclosed (hv.inter isOpen_interior) (subset_inter hsv hsk)
        ((measure_mono hst').trans_lt htμ).ne c hδ.ne'
    refine ⟨F, ?_, hF, hmem, ?_, ?_⟩
    · convert (hhalf _ _ hclose hI).le using 2
      ext q
      simp
    · apply hk.of_isClosed_subset (isClosed_tsupport F)
      exact closure_minimal (hsupp.trans (inter_subset_right.trans interior_subset)) hk.isClosed
    · exact (closure_mono (hsupp.trans inter_subset_left)).trans hvB
  · rintro F G ⟨hF, hmF, hcF, hsF⟩ ⟨hG, hmG, hcG, hsG⟩
    refine ⟨hF.add hG, hmF.add hmG, hcF.add hcG, ?_⟩
    exact (tsupport_add F G).trans (union_subset hsF hsG)

/-- The dense set used in the canonical proof: support is compact in the open ball. -/
def compactContinuousBallClasses (n : ℕ) : Set (BallL2 n) :=
  {f | ∃ F : ℍ → BinaryForm n, Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ball ∧
    ∃ hF : MemLp F 2 (weightedBallMeasure n), f = hF.toLp F}

theorem dense_compactContinuousBallClasses (n : ℕ) (hn : 2 ≤ n) :
    Dense (compactContinuousBallClasses n) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε => ?_
  obtain ⟨F, hclose, hcont, hmem, hc, hs⟩ :=
    exists_compactContinuous_ball_approx n hn (Lp.memLp f) hε.ne'
  refine ⟨hmem.toLp F, ⟨F, hcont, hc, hs, hmem, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

end MathResearch.Spinor
