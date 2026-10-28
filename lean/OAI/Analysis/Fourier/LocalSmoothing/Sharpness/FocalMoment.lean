import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.MomentLower
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PowerIntegral

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

theorem focalMomentExponent {n : ℕ} (hn : 1 ≤ n) (p : ℝ) :
    frequencyMomentExponent n p + (-timeMomentExponent n p-1) =
      (n:ℝ)*p-n-1 := by
  unfold frequencyMomentExponent timeMomentExponent
  rw [Nat.cast_sub hn,Nat.cast_one]
  ring

theorem focusing_packet_focal_moment_lower {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ N : ℝ, 8*A ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^((n:ℝ)*p-n-1)) ≤
      ∫⁻ z, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1‖ₑ^p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
  obtain ⟨A,hA,h⟩ := focusing_packet_integrated_moment_lower hn
  obtain ⟨c,hc,h⟩ := h p hp
  let q := timeMomentExponent n p
  let b := A*min (A^q) ((2*A)^q)
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hb : 0 < b := mul_pos hA0 (lt_min (by positivity) (by positivity))
  refine ⟨c*b,A,mul_pos hc hb,hA,fun N hN f hf => ?_⟩
  have hN0 : 0 < N := (by positivity : 0 < 8*A).trans_le hN
  have he : (c*b)*N^((n:ℝ)*p-n-1) =
      (c*N^(frequencyMomentExponent n p))*(b*N^(-q-1)) := by
    rw [←focalMomentExponent hn p,Real.rpow_add hN0]
    dsimp [q]
    ring
  have hi := lintegral_rpow_focal_interval hA0 hN0 q
  have hs : Icc (A/N) (2*A/N) ⊆ Icc (A/N) (1/4:ℝ) := by
    intro t ht
    exact ⟨ht.1,ht.2.trans ((div_le_iff₀ hN0).2 (by linarith))⟩
  calc
    _ = ENNReal.ofReal (c*N^(frequencyMomentExponent n p))*ENNReal.ofReal (b*N^(-q-1)) := by
      rw [he,ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (c*N^(frequencyMomentExponent n p))*
        (∫⁻ t in Icc (A/N) (2*A/N),ENNReal.ofReal (t^q)) := mul_le_mul' le_rfl hi
    _ ≤ ENNReal.ofReal (c*N^(frequencyMomentExponent n p))*
        (∫⁻ t in Icc (A/N) (1/4:ℝ),ENNReal.ofReal (t^q)) :=
      mul_le_mul' le_rfl (lintegral_mono_set hs)
    _ ≤ _ := h N hN0 f hf

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
