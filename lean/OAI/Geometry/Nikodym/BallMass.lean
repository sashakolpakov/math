import OAI.Geometry.Nikodym.Averaging
import OAI.Geometry.Nikodym.FullStripLp
import OAI.Analysis.Fourier.WavePackets.Young

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

def ballMass {n : ℕ} (R : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ∫⁻ y in ball x R, ‖f y‖ₑ

theorem measurable_ballMass {n : ℕ} (R : ℝ) {f : Space n → ℂ} (hf : Measurable f) :
    Measurable (ballMass R f) := by
  let F : Space n → Space n → ℝ≥0∞ := fun x => (ball x R).indicator (fun y => ‖f y‖ₑ)
  have hm (x) : AEMeasurable (F x) volume := (hf.enorm.indicator isOpen_ball.measurableSet).aemeasurable
  have hl (y) : LowerSemicontinuous (fun x => F x y) := by
    have he : (fun x => F x y) = (ball y R).indicator (fun _ => ‖f y‖ₑ) := by
      funext x
      by_cases hx : x ∈ ball y R
      · have hy : y ∈ ball x R := by simpa only [mem_ball,dist_comm] using hx
        simp [F,hx,hy]
      · have hy : y ∉ ball x R := by simpa only [mem_ball,dist_comm] using hx
        simp [F,hx,hy]
    rw [he]
    exact isOpen_ball.lowerSemicontinuous_indicator bot_le
  have hh := OAI.MeasureTheory.Kakeya.lowerSemicontinuous_lintegral_family F hm hl
  have he : ballMass R f = fun x => ∫⁻ y, F x y := by
    funext x
    exact (lintegral_indicator isOpen_ball.measurableSet (fun y => ‖f y‖ₑ)).symm
  rw [he]
  exact hh.measurable

theorem volume_ball_center {n : ℕ} (R : ℝ) (x : Space n) :
    volume (ball x R) = volume (ball (0:Space n) R) := by
  have h := setLIntegral_translate_ball (volume : Measure (Space n)) x R
    (F:=fun _ => (1:ℝ≥0∞))
  simpa only [lintegral_const,Measure.restrict_apply_univ,one_mul] using h.symm

theorem ballMass_lp_le {d : ℕ} (R : ℝ) {f : Space (d+1) → ℂ} (hf : Measurable f) :
    eLpNorm (ballMass R f) (d+1 : ℕ) volume ≤
      volume (ball (0:Space (d+1)) R) * eLpNorm f (d+1 : ℕ) volume := by
  let A := volume (ball (0:Space (d+1)) R)
  have hA : A ≠ ⊤ := measure_ball_lt_top.ne
  have hpoint (x : Space (d+1)) : ballMass R f x^(d+1) ≤
      A^d * ∫⁻ y in ball x R, ‖f y‖ₑ^(d+1) := by
    have h := OAI.Analysis.Fourier.WavePackets.lintegral_rpow_le_mass_mul (ν:=volume.restrict (ball x R)) hf.enorm
      (p:=(d+1:ℕ)) (by exact_mod_cast Nat.le_add_left 1 d)
    have he : ((d+1:ℕ):ℝ)-1 = (d:ℝ) := by push_cast; ring
    simpa only [ballMass,Measure.restrict_apply_univ,volume_ball_center,he,
      ENNReal.rpow_natCast,A] using h
  have hi := lintegral_mono (μ:=volume) hpoint
  rw [lintegral_const_mul' (A^d) _ (by finiteness),
    lintegral_ball_average volume R (hf.enorm.pow_const (d+1)),← mul_assoc,← pow_succ] at hi
  apply ennreal_le_of_nat_pow_le (n:=d+1) (by omega)
  rw [mul_pow,eLpNorm_nat_pow_eq_lintegral (by omega) (measurable_ballMass R hf).aestronglyMeasurable,
    eLpNorm_nat_pow_eq_lintegral (by omega) hf.aestronglyMeasurable]
  simpa [A] using hi

end OAI.Geometry.Nikodym
