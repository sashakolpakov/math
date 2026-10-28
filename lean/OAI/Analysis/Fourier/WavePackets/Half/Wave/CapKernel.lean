import OAI.Analysis.Fourier.WavePackets.Half.Wave.CapSmooth
import OAI.Analysis.Fourier.WavePackets.Half.Wave.Modulation
import OAI.Analysis.Fourier.WavePackets.AngularCompact

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

theorem capWaveFamily_common_support {d : ℕ} {b : Space (d+1) → ℂ}
    {B : ℝ} (hs : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B) :
    tsupport (capWaveFamily b) ⊆ Set.univ ×ˢ
      (WithLp.toLp 2 '' Set.Icc (fun _ : Fin (d+1) => -B) (fun _ => B)) := by
  intro p hp
  have hx : p ∈ tsupport (fun q : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) =>
      angularChartFamily b (q.1.2,q.2)) := tsupport_mul_subset_left hp
  have hpre := tsupport_comp_subset_preimage (angularChartFamily b)
    (continuous_fst.snd.prodMk continuous_snd) hx
  exact ⟨trivial,(angularChartFamily_common_support hs hpre).2⟩

theorem waveAmplitude_chart_rescale {d : ℕ} {b : Space (d+1) → ℂ}
    {a : ℝ} (ha : 0 < a) (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0)
    {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) (T : ℝ) :
    (waveAmplitude (angularChartSymbol b γ c) (γ^2) T ∘ angularChartLinearEquiv γ hγ c) =
      fun ξ => Complex.exp (-Complex.I*((T/γ^2)*capLinearPhase γ c ξ : ℝ))*
        capWaveFamily b ((T,γ,c),ξ) := by
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hh
    have := hs ξ (subset_tsupport b hh)
    rw [hξ] at this
    linarith
  funext ξ
  have hsym : angularChartSymbol b γ c (angularChartLinearEquiv γ hγ c ξ) =
      angularChartFamily b ((γ,c),ξ) := by
    rw [angularChartSymbol_eq_rescaled hb0 hγ]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  simp only [Function.comp_apply,waveAmplitude,hsym,capWaveFamily]
  by_cases hbξ : b (angularChartRescale γ c ξ) = 0
  · simp [angularChartFamily,hbξ]
  · have hξ : 0 < ξ 0 := by
      have hx := hs (angularChartRescale γ c ξ) (subset_tsupport b hbξ)
      simpa only [angularChartRescale_zero] using ha.trans_le hx
    have hphase : (T/γ^2)*‖angularChartRescale γ c ξ‖ =
        (T/γ^2)*capLinearPhase γ c ξ + T*capPhaseRemainder γ c ξ := by
      have he := capPhaseRemainder_identity γ c ξ hξ
      field_simp
      linear_combination T*he
    change Complex.exp (-Complex.I*((T/γ^2)*‖angularChartRescale γ c ξ‖ : ℝ))*_ = _
    rw [hphase,Complex.ofReal_add,mul_add,Complex.exp_add]
    ring

/-- Each √h projective cap has uniformly bounded half-wave kernel L¹
norm after removing its true linear phase. -/
theorem uniform_wave_angularChart_kernel {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      ∀ c : Fin d → ℝ, (∀ i, |c i| ≤ R) → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude (angularChartSymbol b γ c) (γ^2) T)) 1 volume ≤
        ENNReal.ofReal C := by
  obtain ⟨B,hB,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hslab : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by
    intro ξ hξ
    exact ⟨ne_of_gt (ha.trans_le (hs ξ hξ)),
      (show |ξ 0| ≤ ‖ξ‖ from PiLp.norm_apply_le ξ 0).trans (hbound ξ hξ)⟩
  let K : Set (ℝ × (ℝ × (Fin d → ℝ))) := Icc 1 2 ×ˢ (Icc 0 1 ×ˢ Icc (fun _ => -R) (fun _ => R))
  let S : Set (Space (d+1)) := WithLp.toLp 2 '' Icc (fun _ : Fin (d+1) => -B) (fun _ => B)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hS : IsCompact S := isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hsupp := capWaveFamily_common_support hslab
  have hfamily := contDiff_capWaveFamily hb ha hs
  obtain ⟨C,hC,hkernel⟩ := uniform_linearly_rescaled_inverse_kernel_bound hK hS hfamily hsupp
  refine ⟨C,hC,?_⟩
  intro γ hγ hγ1 c hcR T hT
  let A := angularChartLinearEquiv γ hγ.ne' c
  let f : Space (d+1) → ℂ := fun ξ => capWaveFamily b ((T,γ,c),ξ)
  have hf : ContDiff ℝ ∞ f := hfamily.comp (contDiff_const.prodMk contDiff_id)
  have hfc : HasCompactSupport f := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hsupp (tsupport_comp_subset_preimage (capWaveFamily b)
      (continuous_const.prodMk continuous_id) hξ)).2
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hfc
  have hbγ := contDiff_angularChartSymbol hb ha hs hγ.ne' c
  have hcγ := hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_angularChartSymbol_subset b γ c)
  have hzγ : (0 : Space (d+1)) ∉ tsupport (angularChartSymbol b γ c) := by
    intro h
    have := hs 0 (tsupport_angularChartSymbol_subset b γ c h)
    simp only [PiLp.zero_apply] at this
    linarith
  rw [← eLpNorm_fourierInv_comp_smooth (contDiff_waveAmplitude hbγ hzγ (γ^2) T)
    (hasCompactSupport_waveAmplitude hcγ (γ^2) T) A,
    waveAmplitude_chart_rescale ha hs hγ.ne' c T,
    eLpNorm_fourierInv_cap_modulate hfi]
  simpa only [ContinuousLinearEquiv.refl_apply] using hkernel (T,γ,c)
    ⟨hT,⟨hγ.le,hγ1⟩,⟨fun i => (abs_le.mp (hcR i)).1,fun i => (abs_le.mp (hcR i)).2⟩⟩
    (ContinuousLinearEquiv.refl ℝ (Space (d+1)))

end OAI.Analysis.Fourier.WavePackets
