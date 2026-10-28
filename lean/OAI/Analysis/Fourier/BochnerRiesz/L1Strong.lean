import OAI.Analysis.Fourier.BochnerRiesz.L1Compact
import OAI.Analysis.Fourier.BochnerRiesz.LpStrong

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter Metric
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz


abbrev CompactSchwartz (n : ℕ) :=
  {f : SchwartzMap (Space n) ℂ // HasCompactSupport (f : Space n → ℂ)}

theorem denseRange_compactSchwartz_toLp {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ⊤) :
    DenseRange (fun f : CompactSchwartz n => f.val.toLp p volume) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hgc, hgd, hbound⟩ := MemLp.exist_eLpNorm_sub_le hpt (Fact.out : 1 ≤ p)
    (Lp.memLp f) (show 0 < ε / 2 by positivity)
  let u : CompactSchwartz n := ⟨hgc.toSchwartzMap hgd, hgc⟩
  refine ⟨u.val.toLp p volume, mem_range_self u, ?_⟩
  rw [dist_eq_norm, Lp.norm_def]
  have he : eLpNorm (fun x => (f - u.val.toLp p volume : BrLp n p) x) p volume =
      eLpNorm (fun x => f x - g x) p volume := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub f (u.val.toLp p volume), u.val.coeFn_toLp p volume] with x hx hu
    rw [hx, Pi.sub_apply, hu]
    rfl
  rw [he]
  have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hh : (ENNReal.ofReal (ε / 2)).toReal = ε / 2 := ENNReal.toReal_ofReal (by positivity)
  rw [hh] at H
  exact H.trans_lt (by linarith)

theorem tendsto_bochnerRiesz_L1_compactSchwartz {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) (f : CompactSchwartz n) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f.val x - f.val x) 1 volume)
      atTop (𝓝 0) := by
  obtain ⟨S, hS, hs⟩ := f.property.isBounded.exists_pos_norm_le
  apply tendsto_bochnerRiesz_L1_compact hn hδ f.val hS.le
  intro y hy
  by_contra h
  exact (not_le_of_gt hy) (hs y (subset_tsupport _ h))

/-- The endpoint `L¹` norm-convergence clause uses the integrable radial
kernel and is independent of local smoothing. -/
theorem bochnerRiesz_L1_strong_convergence {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : Ioi (0 : ℝ) → BrLp n 1 →L[ℂ] BrLp n 1,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ R (f : SchwartzMap (Space n) ℂ),
        (T R (f.toLp 1 volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f) ∧
      (∀ f, Tendsto (fun R : ℝ => brLpRadius T R f) atTop (𝓝 f)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.Radial.bochnerRiesz_high_order_all_exponents hn hδ
  let hLp (R : Ioi (0 : ℝ)) (f : SchwartzMap (Space n) ℂ) := (hb 1 le_rfl R R.property f).1
  let T (R : Ioi (0 : ℝ)) := bochnerRieszLpExtend hd.le R (hLp R)
  have hT (R : Ioi (0 : ℝ)) := bochnerRieszLpExtend_properties (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    hd.le R (hLp R) hC.le (fun f => (hb 1 le_rfl R R.property f).2)
  have hs (R : Ioi (0 : ℝ)) (f : SchwartzMap (Space n) ℂ) :
      (T R (f.toLp 1 volume) : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R.val f := by
    rw [(hT R).2 f]
    exact (hLp R f).coeFn_toLp
  refine ⟨C, hC, T, fun R => (hT R).1, hs, ?_⟩
  intro f
  apply tendsto_operators_of_dense_core (denseRange_compactSchwartz_toLp (p := 1) (by norm_num))
    (brLpRadius T) hC.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simpa only [brLpRadius, dite_eq_left hR] using (hT ⟨R, hR⟩).1
  · intro g
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
    apply (tendsto_bochnerRiesz_L1_compactSchwartz hn hδ g).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply eLpNorm_congr_ae
    filter_upwards [hs ⟨R, hR⟩ g.val, g.val.coeFn_toLp 1 volume] with x hx hg
    change OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R g.val x - g.val x =
      brLpRadius T R (g.val.toLp 1 volume) x - g.val.toLp 1 volume x
    simp only [brLpRadius, dite_eq_left hR]
    rw [hx, hg]

end OAI.Analysis.Fourier.BochnerRiesz
