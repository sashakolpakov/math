import OAI.Analysis.Fourier.Restriction.ProductNorm

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_le_norm_pair {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F G H : X → ℂ} (hF : AEStronglyMeasurable F μ)
    (hG : AEStronglyMeasurable G μ) (hH : AEStronglyMeasurable H μ)
    {p W E : ℝ} (hp : 1 ≤ p) (hW : 0 ≤ W) (hE : 0 ≤ E)
    (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ W * (‖G x‖ + ‖H x‖) + E) :
    eLpNorm F (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal W * (eLpNorm G (ENNReal.ofReal p) μ + eLpNorm H (ENNReal.ofReal p) μ) +
      ENNReal.ofReal E * μ univ ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let N : X → ℝ := fun x ↦ ‖G x‖ + ‖H x‖
  have hN : AEStronglyMeasurable N μ := hG.norm.add hH.norm
  have hnorm : eLpNorm N (ENNReal.ofReal p) μ ≤
      eLpNorm G (ENNReal.ofReal p) μ + eLpNorm H (ENNReal.ofReal p) μ := by
    calc
      _ ≤ eLpNorm (fun x ↦ ‖G x‖) (ENNReal.ofReal p) μ +
          eLpNorm (fun x ↦ ‖H x‖) (ENNReal.ofReal p) μ := eLpNorm_add_le hp1
      _ = _ := by rw [eLpNorm_norm G hG, eLpNorm_norm H hH]
  have hconst : eLpNorm (fun _ : X ↦ E) (ENNReal.ofReal p) μ =
      ENNReal.ofReal E * μ univ ^ (1 / p) := by
    rw [eLpNorm_const' _ (by positivity) ENNReal.ofReal_ne_top,
      Real.enorm_eq_ofReal hE, ENNReal.toReal_ofReal hp0.le]
  calc
    _ ≤ eLpNorm (fun x ↦ W * N x + E) (ENNReal.ofReal p) μ :=
      eLpNorm_mono_ae_real hF hbound
    _ ≤ eLpNorm (W • N) (ENNReal.ofReal p) μ + eLpNorm (fun _ : X ↦ E) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le hp1
    _ = ENNReal.ofReal W * eLpNorm N (ENNReal.ofReal p) μ +
        ENNReal.ofReal E * μ univ ^ (1 / p) := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hW, hconst]
    _ ≤ _ := by gcongr

end OAI.Analysis.Fourier.Restriction
