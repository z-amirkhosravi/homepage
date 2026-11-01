module
public import MathResearch.Spinor.LocalL2
public import MathResearch.Spinor.WeakHarmonic

/-! DS2 closedness by the written local L² limit argument. The older
intersection-of-kernels proof is not used in this proof of closedness. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Quaternion BigOperators Topology
open MeasureTheory
namespace MathResearch.Spinor

def localWeakTestVector (n : ℕ) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ)
    (q : ℍ) : BinaryForm n := ballDensity n q • weakTestVector n φ j d q

theorem localWeakTestVector_memLp (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    MemLp (localWeakTestVector n φ j d) 2 (volume.restrict (tsupport φ)) := by
  have hc : Continuous (localWeakTestVector n φ j d) :=
    (continuous_ballDensity n).smul (weakTestVector_continuous n hn φ j d)
  have hw : HasCompactSupport (weakTestVector n φ j d) :=
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (weakTestVector_tsupport n φ j d)
  have hs : HasCompactSupport (localWeakTestVector n φ j d) :=
    hw.smul_left (f := ballDensity n)
  exact hc.memLp_of_hasCompactSupport hs

def localWeakTest (n : ℕ) (hn : 2 ≤ n) (φ : BallTest) (j : Fin 2) (d : Fin 2 →₀ ℕ) :
    Lp (BinaryForm n) 2 (volume.restrict (tsupport φ)) →L[ℂ] ℂ :=
  innerSL ℂ ((localWeakTestVector_memLp n hn φ j d).toLp (localWeakTestVector n φ j d))

theorem weakTest_eq_local (n : ℕ) (hn : 2 ≤ n) (φ : BallTest)
    (j : Fin 2) (d : Fin 2 →₀ ℕ) (f : BallL2 n) :
    weakTest n hn φ j d f = localWeakTest n hn φ j d
      (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset f) := by
  let S : ℍ → ℂ := fun q => ∑ μ : Fin 4,
    (fderiv ℝ φ q (Fueter.coordinateBasis μ) : ℂ) * weakSymbol n μ j d (f q)
  have hz : ∀ q ∉ tsupport φ, S q = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro μ _
    have hd : fderiv ℝ φ q (Fueter.coordinateBasis μ) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x (Fueter.coordinateBasis μ))
        (fun h => hq ((tsupport_fderiv_apply_subset ℝ _) h))
    simp [hd]
  have he : weakTest n hn φ j d f = ∫ q in tsupport φ, S q := by
    rw [← Lp.toLp_coeFn f (Lp.memLp f), weakTest_toLp]
    change (∫ q in Ball, S q) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ball)
      (fun q hq => hz q (fun hh => hq (φ.tsupport_subset hh))),
      setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  rw [he]
  change _ = inner ℂ
    ((localWeakTestVector_memLp n hn φ j d).toLp (localWeakTestVector n φ j d))
    (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset f)
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(localWeakTestVector_memLp n hn φ j d).coeFn_toLp,
    compactL2Restriction_ae n hn φ.hasCompactSupport φ.tsupport_subset f,
    ae_restrict_mem (isClosed_tsupport φ).measurableSet] with q hq₁ hq₂ hqK
  rw [hq₁, hq₂]
  change S q = inner ℂ ((ballDensity n q : ℂ) • weakTestVector n φ j d q) (f q)
  rw [inner_smul_left]
  simpa using (weakTestVector_pairing n hn φ j d (f q) (φ.tsupport_subset hqK)).symm

/-- The distributional equation passes to a limit in ordinary L² on the
compact support of every test, exactly as asserted in the written proof. -/
theorem weakKernel_closed_under_localL2_limits (n : ℕ) (hn : 2 ≤ n)
    {f : ℕ → BallL2 n} {g : BallL2 n} (hf : ∀ k, f k ∈ weakKernel n hn)
    (hlim : ∀ φ : BallTest, Filter.Tendsto
      (fun k => compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset (f k))
      Filter.atTop (𝓝 (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset g))) :
    g ∈ weakKernel n hn := by
  rw [mem_weakKernel]
  intro φ j d
  have ht := ((localWeakTest n hn φ j d).continuous.tendsto
    (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset g)).comp (hlim φ)
  have hz : (fun k => localWeakTest n hn φ j d
      (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset (f k))) = fun _ => 0 := by
    funext k
    rw [← weakTest_eq_local]
    exact (mem_weakKernel n hn (f k)).mp (hf k) φ j d
  change Filter.Tendsto (fun k => localWeakTest n hn φ j d
    (compactL2Restriction n hn φ.hasCompactSupport φ.tsupport_subset (f k))) _ _ at ht
  rw [hz] at ht
  rw [weakTest_eq_local]
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- Closedness via the actual compact-subset convergence argument in DS2. -/
theorem weakKernel_isClosed_by_localL2 (n : ℕ) (hn : 2 ≤ n) :
    IsClosed (weakKernel n hn : Set (BallL2 n)) := by
  apply IsSeqClosed.isClosed
  intro f g hf hlim
  exact weakKernel_closed_under_localL2_limits n hn hf (fun φ =>
    weightedL2_tendsto_locally n hn φ.hasCompactSupport φ.tsupport_subset hlim)

end MathResearch.Spinor
