import OAI.Analysis.Fourier.Restriction.Local

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def restrictionModulate {n : ℕ} (v : Space n) (f : Space n → ℂ) (x : Space n) : ℂ :=
  Complex.exp (-Complex.I * ((inner ℝ x v : ℝ) : ℂ)) * f x

theorem norm_restrictionModulate {n : ℕ} (v : Space n) (f : Space n → ℂ) (x : Space n) :
    ‖restrictionModulate v f x‖ = ‖f x‖ := by
  simp [restrictionModulate, Complex.norm_exp]

theorem measurable_restrictionModulate {n : ℕ} (v : Space n) {f : Space n → ℂ}
    (hf : Measurable f) : Measurable (restrictionModulate v f) := by
  unfold restrictionModulate
  fun_prop

theorem integrable_restrictionModulate {n : ℕ} (v : Space n) {f : Space n → ℂ}
    (hf : Integrable f) : Integrable (restrictionModulate v f) := by
  apply hf.norm.mono'
  · exact ((show Continuous (fun x : Space n ↦ Complex.exp (-Complex.I * ((inner ℝ x v : ℝ) : ℂ)))
      by fun_prop).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ (norm_restrictionModulate v f x).le

theorem eLpNorm_restrictionModulate {n : ℕ} (v : Space n) {f : Space n → ℂ}
    (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (restrictionModulate v f) p volume = eLpNorm f p volume := by
  exact eLpNorm_congr_norm_ae (measurable_restrictionModulate v hf).aestronglyMeasurable
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (norm_restrictionModulate v f))

theorem angularFourier_restrictionModulate {n : ℕ} (v : Space n) (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (restrictionModulate v f) ξ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ξ + v) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularFourier restrictionModulate
  apply integral_congr_ae
  filter_upwards [] with x
  rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

theorem localSmoothing_local_restriction_translated (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R → ∀ f : Space n → ℂ,
      Measurable f → Integrable f → (∀ x, R < ‖x‖ → f x = 0) → ∀ v : Space n,
      eLpNorm (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ω + v)) (ENNReal.ofReal (restrictionInputExponent n))
        (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * ENNReal.ofReal (R ^ ε) * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  obtain ⟨C, hC, H⟩ := localSmoothing_local_restriction hls hn hε
  refine ⟨C, hC, ?_⟩
  intro R hR f hfm hfi hfs v
  have HM := H R hR (restrictionModulate v f) (measurable_restrictionModulate v hfm)
    (integrable_restrictionModulate v hfi) (fun x hx ↦ by simp [restrictionModulate, hfs x hx])
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularFourier (restrictionModulate v f) = fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ω + v) :=
    funext (angularFourier_restrictionModulate v f)
  rwa [he, eLpNorm_restrictionModulate v hfm] at HM

end OAI.Analysis.Fourier.Restriction
