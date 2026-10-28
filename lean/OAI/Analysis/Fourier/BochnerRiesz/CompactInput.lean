import OAI.Analysis.Fourier.BochnerRiesz.CompactApprox
import OAI.Analysis.Fourier.Radial.BRConjecture

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem norm_convolveKernel_sub_le {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} (hK : Continuous K) {B : ℝ}
    (hB : ∀ x, ‖K x‖ ≤ B) {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) {ε : ℝ} (hε : 0 ≤ ε)
    (he : eLpNorm (f - g) 1 volume ≤ ENNReal.ofReal ε) (x : Space n) :
    ‖OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x - OAI.Analysis.Fourier.SquareFunction.convolveKernel K g x‖ ≤ ε * B := by
  have hBb : BddAbove (range fun x => ‖K x‖) :=
    ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  have hB0 : 0 ≤ B := (norm_nonneg (K 0)).trans (hB 0)
  have hei : (∫ y, ‖(f - g) y‖) ≤ ε := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf.sub hg).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hf.sub hg)] at he
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp he
  have hid : f = g + (f - g) := by ext y; simp
  have hsum := congrFun ((congrArg (OAI.Analysis.Fourier.SquareFunction.convolveKernel K) hid).trans
    (OAI.Analysis.Fourier.SquareFunction.convolveKernel_add hK hBb hg (hf.sub hg))) x
  rw [hsum, add_sub_cancel_left]
  exact (OAI.Analysis.Fourier.SquareFunction.norm_convolveKernel_le (hf.sub hg) hK hB x).trans
    (mul_le_mul_of_nonneg_right hei hB0)

/-- Compact support permits simultaneous `L¹` and `Lᵖ` approximation, so an
integrability assumption on the convolution kernel is unnecessary. -/
theorem convolution_bound_of_schwartz_compact {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} (hK : Continuous K)
    (hKb : BddAbove (range fun x => ‖K x‖)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.convolveKernel K g) p volume ≤ A * eLpNorm g p volume)
    {f : Space n → ℂ} (hfi : Integrable f) (hfp : MemLp f p volume)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, R < ‖x‖ → f x = 0) :
    eLpNorm (OAI.Analysis.Fourier.SquareFunction.convolveKernel K f) p volume ≤ A * eLpNorm f p volume := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k) : 0 < ε k := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose g hgp hg1 using fun k =>
    exists_schwartz_compact_approx_two_norms hp hpt hfi.aestronglyMeasurable hfp hR hs (hε k)
  obtain ⟨B, hB⟩ := hKb
  have hB' (x) : ‖K x‖ ≤ B := hB (mem_range_self x)
  have hKb : BddAbove (range fun x => ‖K x‖) := ⟨B, hB⟩
  have hlim (x) : Tendsto (fun k => OAI.Analysis.Fourier.SquareFunction.convolveKernel K (g k) x) atTop
      (𝓝 (OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun k => norm_nonneg _) _ (by simpa using hεlim.mul_const B)
    intro k
    rw [norm_sub_rev]
    exact norm_convolveKernel_sub_le hK hB' hfi (g k).integrable (hε k).le (hg1 k) x
  have hnorm (k) : eLpNorm (g k) p volume ≤ eLpNorm f p volume + ENNReal.ofReal (ε k) := by
    have hid : (g k : Space n → ℂ) = f - (f - (g k : Space n → ℂ)) := by ext x; simp
    rw [hid]
    exact (eLpNorm_sub_le hp).trans (add_le_add le_rfl (hgp k))
  have hb (k) : eLpNorm (OAI.Analysis.Fourier.SquareFunction.convolveKernel K (g k)) p volume ≤
      A * (eLpNorm f p volume + ENNReal.ofReal (ε k)) :=
    (hbound (g k)).trans (mul_le_mul' le_rfl (hnorm k))
  have hright : Tendsto (fun k => A * (eLpNorm f p volume + ENNReal.ofReal (ε k)))
      atTop (𝓝 (A * eLpNorm f p volume)) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hεlim
    simpa using ENNReal.Tendsto.const_mul
      ((tendsto_const_nhds (x := eLpNorm f p volume)).add he) (Or.inr hA)
  calc
    _ ≤ atTop.liminf (fun k => eLpNorm (OAI.Analysis.Fourier.SquareFunction.convolveKernel K (g k)) p volume) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm
        (fun k => (OAI.Analysis.Fourier.SquareFunction.continuous_convolveKernel (g k).integrable hK hKb).aestronglyMeasurable)
        _ (OAI.Analysis.Fourier.SquareFunction.continuous_convolveKernel hfi hK hKb).aestronglyMeasurable
        (Eventually.of_forall hlim)
    _ ≤ atTop.liminf (fun k => A * (eLpNorm f p volume + ENNReal.ofReal (ε k))) :=
      liminf_le_liminf (Eventually.of_forall hb)
    _ = _ := hright.liminf_eq

theorem convolveKernel_bochnerRiesz_eq {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {f : Space n → ℂ} (hf : Integrable f) :
    OAI.Analysis.Fourier.SquareFunction.convolveKernel (OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ) f = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 f := by
  rw [OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz_eq_frequencyHalfWave δ (by norm_num : (0 : ℝ) < 1)]
  funext x
  rw [OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_convolution
    (φ := fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ))
    (Complex.continuous_ofReal.comp (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hδ.le 1))
    (OAI.Analysis.Fourier.Radial.hasCompactSupport_complex_bochnerRieszSymbol_unit hδ) (by norm_num) hf]
  simp only [inv_one, one_smul]
  rw [OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
  unfold OAI.Analysis.Fourier.WavePackets.complexConvolution OAI.Analysis.Fourier.Radial.bochnerRieszKernel
  congr 1
  funext y
  simp only [smul_eq_mul, mul_comm]

theorem bddAbove_norm_bochnerRieszKernel {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) :
    BddAbove (range fun x : Space n => ‖OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ x‖) := by
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.Radial.bochnerRieszKernel_polynomial_decay hn hδ
  refine ⟨C, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply (hb x).trans
  calc
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)) hC.le
    _ = C := mul_one _

/-- The classical unit-radius convolution estimate on compactly supported
`L¹ ∩ Lᵖ` inputs. The constant is independent of the support radius. -/
theorem localSmoothing_bochnerRiesz_compact_convolution (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {δ : ℝ} (hδ : OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszIndex n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ, Integrable f → MemLp f p volume →
      ∀ R : ℝ, 0 ≤ R → (∀ x, R < ‖x‖ → f x = 0) →
      MemLp (fun x => ∫ y, OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (x - y) * f y) p volume ∧
      eLpNorm (fun x => ∫ y, OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (x - y) * f y) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  have hd : 0 < δ := lt_of_le_of_lt (le_max_right _ _) hδ
  obtain ⟨C, hC, hb⟩ := OAI.Analysis.Fourier.Radial.localSmoothing_bochnerRieszConjecture hls n hn p hp δ hδ
  refine ⟨C, hC, fun f hf hfp R hR hs => ?_⟩
  have he : (fun x => ∫ y, OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ (x - y) * f y) =
      OAI.Analysis.Fourier.SquareFunction.convolveKernel (OAI.Analysis.Fourier.Radial.bochnerRieszKernel δ) f := by
    funext x
    unfold OAI.Analysis.Fourier.SquareFunction.convolveKernel
    congr 1
    funext y
    simp only [smul_eq_mul, mul_comm]
  rw [he]
  have H := convolution_bound_of_schwartz_compact
    (OAI.Analysis.Fourier.Radial.continuous_bochnerRieszKernel hd) (bddAbove_norm_bochnerRieszKernel (by omega) hd)
    hp hpt ENNReal.ofReal_ne_top
    (fun g => by
      rw [convolveKernel_bochnerRiesz_eq hd g.integrable]
      exact (hb 1 (by norm_num) g).2) hf hfp hR hs
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp), H⟩

end OAI.Analysis.Fourier.BochnerRiesz
