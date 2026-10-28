import OAI.Geometry.Nikodym.DilationLp
import OAI.Geometry.Nikodym.FullStripLp

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def scaledStrip {d : ℕ} (δ V r : ℝ) (f : Space (d+1) → ℂ) (x : Space (d+1)) : ℝ≥0∞ :=
  ENNReal.ofReal |r| * fullStrip (δ/|r|) V (fun y => f (r • y)) (r⁻¹ • x)

theorem measurable_scaledStrip {d : ℕ} (δ V r : ℝ) {f : Space (d+1) → ℂ}
    (hf : Measurable f) : Measurable (scaledStrip δ V r f) :=
  measurable_const.mul ((measurable_fullStrip _ _ (hf.comp (measurable_const_smul r))).comp
    (measurable_const_smul r⁻¹))

theorem scaledStrip_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, r ≠ 0 → 0 < δ → δ/|r| ≤ 1/2 →
      stripDilation V*(δ/|r|) ≤ 1 → ∀ f : Space (d+1) → ℂ,
      Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (scaledStrip δ V r f) (d+1 : ℕ) volume ≤
          ENNReal.ofReal (C * |r| * (δ/|r|)^(-ε)) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,hbound⟩ := fullStrip_lp_bound hK hd hV hε
  refine ⟨C,hC,?_⟩
  intro r δ hr hδ hh hD f hf hfp
  have hrp : 0 < |r| := abs_pos.mpr hr
  have hfr : Measurable (fun y => f (r • y)) := hf.comp (measurable_const_smul r)
  have hn := eLpNorm_dilate_dimension (by omega : 0 < d+1) hf.aestronglyMeasurable hr
  have hmem : MemLp (fun y => f (r • y)) (d+1 : ℕ) volume := by
    change eLpNorm _ _ _ < ⊤
    rw [hn]
    exact ENNReal.mul_lt_top (by finiteness) hfp
  have hb := hbound (δ/|r|) (div_pos hδ hrp) hh hD _ hfr hmem
  rw [hn] at hb
  have hs := eLpNorm_dilate_dimension (by omega : 0 < d+1)
    (measurable_fullStrip (δ/|r|) V hfr).aestronglyMeasurable (inv_ne_zero hr)
  have hnorm : eLpNorm (scaledStrip δ V r f) (d+1 : ℕ) volume ≤
      ENNReal.ofReal |r| * eLpNorm
        (fun x => fullStrip (δ/|r|) V (fun y => f (r • y)) (r⁻¹ • x)) (d+1 : ℕ) volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ (measurable_scaledStrip δ V r hf).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simp [scaledStrip])
  rw [hs,abs_inv,ENNReal.ofReal_inv_of_pos hrp,inv_inv] at hnorm
  apply hnorm.trans ((mul_le_mul' le_rfl (mul_le_mul' le_rfl hb)).trans_eq ?_)
  have h0 : ENNReal.ofReal |r| ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hrp)
  have ht : ENNReal.ofReal |r| ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_mul (mul_nonneg hC.le hrp.le)]
  calc
    _ = ENNReal.ofReal C * ENNReal.ofReal |r| * ENNReal.ofReal ((δ/|r|)^(-ε)) *
        (ENNReal.ofReal |r| * (ENNReal.ofReal |r|)⁻¹) * eLpNorm f (d+1 : ℕ) volume := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel h0 ht,mul_one,ENNReal.ofReal_mul hC.le]

theorem scaledStrip_lp_bound_small (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, r ≠ 0 → |r| ≤ 1 → 0 < δ →
      stripDilation V*δ ≤ |r| → ∀ f : Space (d+1) → ℂ,
      Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (scaledStrip δ V r f) (d+1 : ℕ) volume ≤
          ENNReal.ofReal (C * δ^(-ε) * |r|) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,h⟩ := scaledStrip_lp_bound hK hd hV hε
  refine ⟨C,hC,?_⟩
  intro r δ hr hr1 hδ hcut f hf hfp
  have hrp := abs_pos.mpr hr
  have hD : 2 ≤ stripDilation V := by dsimp [stripDilation]; linarith
  have hh : δ/|r| ≤ 1/2 := (div_le_iff₀ hrp).mpr (by nlinarith)
  have hDη : stripDilation V*(δ/|r|) ≤ 1 := by
    rw [← mul_div_assoc,div_le_one hrp]
    exact hcut
  have hη : δ ≤ δ/|r| := (le_div_iff₀ hrp).mpr (by nlinarith)
  have hp := Real.rpow_le_rpow_of_nonpos hδ hη (neg_nonpos.mpr hε.le)
  apply (h r δ hr hδ hh hDη f hf hfp).trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc
    C * |r| * (δ/|r|)^(-ε) ≤ C * |r| * δ^(-ε) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hrp.le)
    _ = _ := by ring

end OAI.Geometry.Nikodym
