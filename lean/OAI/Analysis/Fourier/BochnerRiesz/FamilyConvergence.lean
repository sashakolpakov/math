import OAI.Analysis.Fourier.BochnerRiesz.AEConvergence

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem aestronglyMeasurable_brFamilyRepresentative {n : ℕ} {p : ℝ≥0∞}
    (F : BrFamilyLp n p) (R : ℝ) :
    AEStronglyMeasurable (brFamilyRepresentative F R) volume :=
  (ContinuousMap.evalCLM ℂ (inverseRadiusAt R)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)

theorem tendsto_eLpNorm_brFamilyRepresentative {n : ℕ} {p : ℝ≥0∞}
    (hp : p ≠ 0) (hpt : p ≠ ⊤) (F : BrFamilyLp n p) :
    Tendsto (fun R => eLpNorm (fun x => brFamilyRepresentative F R x - F x inverseRadiusZero)
      p volume) atTop (𝓝 0) := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp hpt
  let G : ℝ → Space n → ℂ := fun R x => brFamilyRepresentative F R x - F x inverseRadiusZero
  have hm (R) : AEStronglyMeasurable (G R) volume :=
    (aestronglyMeasurable_brFamilyRepresentative F R).sub
      ((ContinuousMap.evalCLM ℂ inverseRadiusZero).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
  have hb (R x) : ‖G R x‖ₑ ≤ 2 * ‖F x‖ₑ := by
    apply enorm_sub_le.trans
    have h (τ : InverseRadius) : ‖F x τ‖ₑ ≤ ‖F x‖ₑ := by
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (ContinuousMap.norm_coe_le_norm (F x) τ)
    exact (add_le_add (h (inverseRadiusAt R)) (h inverseRadiusZero)).trans_eq (two_mul _).symm
  have hi : (∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂volume) ≠ ⊤ :=
    ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp hpt (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)).ne
  have hi' : (∫⁻ x, (2 * ‖F x‖ₑ) ^ p.toReal ∂volume) ≠ ⊤ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hpR.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpR.le (by norm_num))]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hpR.le (by norm_num)) hi
  have hlim (x) : Tendsto (fun R => ‖G R x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    have hG : Tendsto (fun R => G R x) atTop (𝓝 0) := by
      simpa only [sub_self] using (tendsto_brFamilyRepresentative F x).sub
        (tendsto_const_nhds (x := F x inverseRadiusZero))
    have hnorm := continuous_enorm.continuousAt.tendsto.comp hG
    have H := (ENNReal.continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp hnorm
    simpa only [Function.comp_def, enorm_zero, ENNReal.zero_rpow_of_pos hpR] using H
  have H := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := (volume : Measure (Space n))) (fun x => (2 * ‖F x‖ₑ) ^ p.toReal)
    (F := fun R x => ‖G R x‖ₑ ^ p.toReal) (f := fun _ => 0)
    (Eventually.of_forall fun R => (hm R).enorm.pow_const _)
    (Eventually.of_forall fun R => Eventually.of_forall fun x => ENNReal.rpow_le_rpow (hb R x) hpR.le)
    hi' (Eventually.of_forall hlim)
  have H' := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp H
  change Tendsto (fun R => eLpNorm (G R) p volume) atTop (𝓝 0)
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hpt (hm _)]
  simpa only [Function.comp_def, lintegral_zero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpR)] using H'

theorem tendsto_brFamilyEval {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ⊤) (F : BrFamilyLp n p) :
    Tendsto (fun R => brFamilyEval (inverseRadiusAt R) F) atTop
      (𝓝 (brFamilyEval inverseRadiusZero F)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  have hp : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have H := tendsto_eLpNorm_brFamilyRepresentative hp hpt F
  apply H.congr'
  apply Eventually.of_forall
  intro R
  apply eLpNorm_congr_ae
  filter_upwards [brFamilyEval_coe (inverseRadiusAt R) F, brFamilyEval_coe inverseRadiusZero F]
    with x hx hz
  exact (congrArg₂ (· - ·) hx hz).symm

theorem norm_brFamilyEval_apply_le {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (τ : InverseRadius) (F : BrFamilyLp n p) : ‖brFamilyEval τ F‖ ≤ ‖F‖ := by
  let L : C(InverseRadius, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ τ
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    change ‖g τ‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using ContinuousMap.norm_coe_le_norm g τ
  calc
    ‖brFamilyEval τ F‖ ≤ ‖L‖ * ‖F‖ := L.norm_compLp_le F
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖F‖ := one_mul _

/-- Large-radius Bochner--Riesz operators on the whole `Lᵖ` space, with
both norm convergence and a coherent almost-everywhere convergent version. -/
theorem localSmoothing_bochnerRiesz_Lp_summability (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∃ T : ℝ → (BrLp n (ENNReal.ofReal p) →L[ℂ] BrLp n (ENNReal.ofReal p)),
    ∃ V : BrLp n (ENNReal.ofReal p) → ℝ → Space n → ℂ,
      (∀ R, ‖T R‖ ≤ C) ∧
      (∀ f R, (T R f : Space n → ℂ) =ᵐ[volume] V f R) ∧
      (∀ f : SchwartzMap (Space n) ℂ, ∀ᵐ x ∂volume, ∀ R : ℝ, 1 ≤ R →
        V (f.toLp (ENNReal.ofReal p) volume) R x = OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f x) ∧
      (∀ f, Tendsto (fun R => T R f) atTop (𝓝 f)) ∧
      (∀ f, ∀ᵐ x ∂volume, Tendsto (fun R => V f R x) atTop (𝓝 (f x))) := by
  obtain ⟨C, hC, U, hUnorm, hUs, hUzero⟩ := localSmoothing_brFamilyLp_operator hls hn hp hδ
  let T := fun R : ℝ => (brFamilyEval (inverseRadiusAt R)).comp U
  let V := fun f => brFamilyRepresentative (U f)
  refine ⟨C, hC, T, V, ?_, ?_, ?_, ?_, ?_⟩
  · intro R
    apply ContinuousLinearMap.opNorm_le_bound _ hC.le
    intro f
    exact (norm_brFamilyEval_apply_le _ (U f)).trans
      ((U.le_opNorm f).trans (mul_le_mul_of_nonneg_right hUnorm (norm_nonneg _)))
  · intro f R
    exact brFamilyEval_coe (inverseRadiusAt R) (U f)
  · exact brFamilyRepresentative_schwartz ((le_max_left _ _).trans hδ.le) U hUs
  · intro f
    have H := tendsto_brFamilyEval ENNReal.ofReal_ne_top (U f)
    rw [hUzero f] at H
    exact H
  · exact ae_tendsto_brFamilyRepresentative U hUzero

end OAI.Analysis.Fourier.BochnerRiesz
