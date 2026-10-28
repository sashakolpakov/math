import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocalMoment
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.NormFromMoment

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

theorem focusing_packet_focal_norm_lower {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ N : ℝ, 8*A ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^((n:ℝ)-(n+1)/p)) ≤
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  obtain ⟨c,A,hc,hA,h⟩ := focusing_packet_focal_moment_lower hn hp.le
  refine ⟨c^(1/p),A,by positivity,hA,fun N hN f hf => ?_⟩
  have hN0 : 0 < N := (by nlinarith : 0 < 8*A).trans_le hN
  have hl := norm_lower_of_moment (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).aestronglyMeasurable hp
    (by positivity : 0 ≤ c*N^((n:ℝ)*p-n-1)) (h N hN f hf)
  have he : ((n:ℝ)*p-n-1)*(1/p) = (n:ℝ)-(n+1)/p := by field_simp; ring
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hN0.le _),←Real.rpow_mul hN0.le,he] at hl
  exact hl

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
