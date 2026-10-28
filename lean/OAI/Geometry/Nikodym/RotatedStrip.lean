import OAI.Geometry.Nikodym.ScaledStripMass

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def rotatedStrip {d : ℕ} (δ V r : ℝ) (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1))
    (f : Space (d+1) → ℂ) (x : Space (d+1)) : ℝ≥0∞ :=
  scaledStrip δ V r (f ∘ L.symm) (L x)

theorem measurable_rotatedStrip {d : ℕ} (δ V r : ℝ)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) {f : Space (d+1) → ℂ} (hf : Measurable f) :
    Measurable (rotatedStrip δ V r L f) :=
  (measurable_scaledStrip δ V r (hf.comp L.symm.continuous.measurable)).comp L.continuous.measurable

theorem rotatedStrip_average_le {d : ℕ} {δ V r : ℝ} (hδ : 0 < δ) (hr : r ≠ 0)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) {v : Space d} (hv : ‖v‖ ≤ V)
    {f : Space (d+1) → ℂ} (hf : Measurable f) (x : Space (d+1)) :
    (∫⁻ y in L ⁻¹' neighborhood δ (scaledLinePiece (L x) v r), ‖f y‖ₑ) /
      ENNReal.ofReal (δ^d) ≤ rotatedStrip δ V r L f x := by
  have h := L.measurePreserving.setLIntegral_comp_preimage
    (isOpen_neighborhood δ (scaledLinePiece (L x) v r)).measurableSet
    (hf.comp L.symm.continuous.measurable).enorm
  simp only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] at h
  rw [h]
  exact linePiece_average_le_scaledStrip hδ hr hv (hf.comp L.symm.continuous.measurable) (L x)

theorem rotatedStrip_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, r ≠ 0 → |r| ≤ 1 → 0 < δ →
      stripDilation V*δ ≤ |r| → ∀ L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1),
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
        eLpNorm (rotatedStrip δ V r L f) (d+1 : ℕ) volume ≤
          ENNReal.ofReal (C * δ^(-ε) * |r|) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨C,hC,h⟩ := scaledStrip_lp_bound_small hK hd hV hε
  refine ⟨C,hC,?_⟩
  intro r δ hr hr1 hδ hcut L f hf hfp
  have hfm : Measurable (f ∘ L.symm) := hf.comp L.symm.continuous.measurable
  have hn := eLpNorm_comp_measurePreserving (p:=(d+1 : ℕ)) hf.aestronglyMeasurable L.symm.measurePreserving
  have hmp : MemLp (f ∘ L.symm) (d+1 : ℕ) volume := by
    change eLpNorm _ _ _ < ⊤
    rw [hn]
    exact hfp
  have hout := eLpNorm_comp_measurePreserving (p:=(d+1 : ℕ))
    (measurable_scaledStrip δ V r hfm).aestronglyMeasurable L.measurePreserving
  change eLpNorm (scaledStrip δ V r (f ∘ L.symm) ∘ L) _ _ ≤ _
  rw [hout]
  simpa only [hn] using h r δ hr hr1 hδ hcut (f ∘ L.symm) hfm hmp

end OAI.Geometry.Nikodym
