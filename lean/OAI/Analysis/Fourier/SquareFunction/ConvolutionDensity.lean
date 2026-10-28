import OAI.Analysis.Fourier.SquareFunction.VectorYoung
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open OAI.Analysis.Fourier.Wave

/-! Transfer an `Lᵖ` convolution estimate from Schwartz functions to the
integrable inputs appearing in the local square-function decomposition. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal NNReal

theorem exists_schwartz_eLpNorm_sub_le {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : Space n → ℂ} (hf : MemLp f p volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap (Space n) ℂ,
      eLpNorm (f - (g : Space n → ℂ)) p volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hc, hd, hbound⟩ := MemLp.exist_eLpNorm_sub_le hpt hp hf hε
  exact ⟨hc.toSchwartzMap hd, hbound⟩

theorem exists_pos_mul_ofReal_le {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℝ≥0} (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ C * ENNReal.ofReal η ≤ ε := by
  have he : 0 < (ε : ℝ) := hε
  refine ⟨(ε : ℝ) / (C.toReal + 1), by positivity, ?_⟩
  have hb : C.toReal * ((ε : ℝ) / (C.toReal + 1)) ≤ ε := by
    calc
      _ ≤ (C.toReal + 1) * ((ε : ℝ) / (C.toReal + 1)) := by
        gcongr
        linarith
      _ = ε := mul_div_cancel₀ _ (by positivity)
  rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    using ENNReal.ofReal_le_ofReal hb

theorem convolveKernel_add {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} (hK : Continuous K) (hB : BddAbove (range fun x => ‖K x‖))
    {f g : Space n → ℂ} (hf : Integrable f) (hg : Integrable g) :
    convolveKernel K (f + g) = fun x => convolveKernel K f x + convolveKernel K g x := by
  funext x
  unfold convolveKernel
  simp only [Pi.add_apply, add_smul]
  exact integral_add (integrable_convolveKernel_integrand hf hK hB x)
    (integrable_convolveKernel_integrand hg hK hB x)

theorem convolution_bound_of_schwartz {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} (hK : Continuous K) (hKi : Integrable K)
    (hKb : BddAbove (range fun x => ‖K x‖)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (convolveKernel K g) p volume ≤ A * eLpNorm g p volume)
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f) (hfp : MemLp f p volume) :
    eLpNorm (convolveKernel K f) p volume ≤ A * eLpNorm f p volume := by
  let B := eLpNorm K 1 volume
  have hB : B ≠ ⊤ := (memLp_one_iff_integrable.mpr hKi).ne
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨η, hη, herror⟩ := exists_pos_mul_ofReal_le (C := A + B)
    (ENNReal.add_ne_top.2 ⟨hA, hB⟩) hε
  obtain ⟨g, hg⟩ := exists_schwartz_eLpNorm_sub_le hp hpt hfp hη
  have hgm : Measurable (g : Space n → ℂ) := g.continuous.measurable
  have hnormg : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal η := by
    have hid : (g : Space n → ℂ) = f - (f - (g : Space n → ℂ)) := by ext x; simp
    calc
      _ = eLpNorm (f - (f - (g : Space n → ℂ))) p volume := congrArg (fun u => eLpNorm u p volume) hid
      _ ≤ eLpNorm f p volume + eLpNorm (f - (g : Space n → ℂ)) p volume := eLpNorm_sub_le hp
      _ ≤ _ := add_le_add le_rfl hg
  have hsum : convolveKernel K f =
      fun x => convolveKernel K g x + convolveKernel K (f - (g : Space n → ℂ)) x := by
    have hid : f = (g : Space n → ℂ) + (f - (g : Space n → ℂ)) := by ext x; simp
    exact (congrArg (convolveKernel K) hid).trans
      (convolveKernel_add hK hKb g.integrable (hfi.sub g.integrable))
  calc
    _ = eLpNorm (fun x => convolveKernel K g x + convolveKernel K (f - (g : Space n → ℂ)) x) p volume :=
      congrArg (fun u => eLpNorm u p volume) hsum
    _ ≤ eLpNorm (convolveKernel K g) p volume +
        eLpNorm (convolveKernel K (f - (g : Space n → ℂ))) p volume := eLpNorm_add_le hp
    _ ≤ A * eLpNorm g p volume + B * eLpNorm (f - (g : Space n → ℂ)) p volume :=
      add_le_add (hbound g) (eLpNorm_convolveKernel_le hK (hfm.sub hgm) hp hpt)
    _ ≤ A * (eLpNorm f p volume + ENNReal.ofReal η) + B * ENNReal.ofReal η := by
      gcongr
    _ = A * eLpNorm f p volume + (A + B) * ENNReal.ofReal η := by ring
    _ ≤ _ := add_le_add le_rfl herror

theorem convolution_bound_of_schwartz_ae {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} (hK : Continuous K) (hKi : Integrable K)
    (hKb : BddAbove (range fun x => ‖K x‖)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (convolveKernel K g) p volume ≤ A * eLpNorm g p volume)
    {f : Space n → ℂ} (hfi : Integrable f) (hfp : MemLp f p volume) :
    eLpNorm (convolveKernel K f) p volume ≤ A * eLpNorm f p volume := by
  let g := hfi.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hfi.aestronglyMeasurable.ae_eq_mk
  have hcg : convolveKernel K f = convolveKernel K g := by
    funext x
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  rw [hcg, eLpNorm_congr_ae hfg]
  have hgp : MemLp g p volume := by
    change eLpNorm g p volume < ⊤
    rw [← eLpNorm_congr_ae hfg]
    exact hfp
  exact convolution_bound_of_schwartz hK hKi hKb hp hpt hA hbound
    hfi.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hfi.congr hfg) hgp

end OAI.Analysis.Fourier.SquareFunction
