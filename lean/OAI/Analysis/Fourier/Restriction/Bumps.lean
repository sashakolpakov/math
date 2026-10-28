import OAI.Analysis.Fourier.Restriction.Translations
import OAI.Analysis.Fourier.Restriction.BoundedInput

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def smallBallBump {n : ℕ} : Space n → ℂ :=
  (ball 0 (1 / 4)).indicator (fun _ ↦ 1)

def separatedBumpSum {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ) : Space n → ℂ :=
  fun x ↦ ∑ z ∈ E, a z * smallBallBump (x - z)

def finitePhaseSum {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ) : Space n → ℂ :=
  fun ξ ↦ ∑ z ∈ E, a z * Complex.exp (-Complex.I * ((inner ℝ z ξ : ℝ) : ℂ))

theorem smallBallBump_translate {n : ℕ} (z x : Space n) :
    smallBallBump (x - z) = (ball z (1 / 4)).indicator (fun _ ↦ (1 : ℂ)) x := by
  have he : x - z ∈ ball (0 : Space n) (1 / 4) ↔ x ∈ ball z (1 / 4) := by
    simp only [mem_ball, dist_eq_norm, sub_zero]
  unfold smallBallBump
  by_cases hx : x ∈ ball z (1 / 4)
  · rw [indicator_of_mem (he.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h ↦ hx (he.mp h)), indicator_of_notMem hx]

theorem measurable_smallBallBump_translate {n : ℕ} (z : Space n) :
    Measurable (fun x ↦ smallBallBump (x - z)) := by
  simp_rw [smallBallBump_translate]
  exact measurable_const.indicator measurableSet_ball

theorem integrable_smallBallBump_translate {n : ℕ} (z : Space n) :
    Integrable (fun x ↦ smallBallBump (x - z)) := by
  simp_rw [smallBallBump_translate]
  have H : IntegrableOn (fun _ : Space n ↦ (1 : ℂ)) (ball z (1 / 4)) volume :=
    integrableOn_const (measure_ball_lt_top.ne)
  exact (integrable_indicator_iff measurableSet_ball).mpr H

theorem measurable_separatedBumpSum {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ) :
    Measurable (separatedBumpSum E a) := by
  apply Finset.measurable_sum
  intro z hz
  exact (measurable_smallBallBump_translate z).const_mul (a z)

theorem integrable_separatedBumpSum {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ) :
    Integrable (separatedBumpSum E a) := by
  apply integrable_finsetSum
  intro z hz
  exact (integrable_smallBallBump_translate z).const_mul (a z)

theorem separatedBumpSum_eq_zero {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ)
    (x : Space n) (hx : ∀ z ∈ E, x ∉ ball z (1 / 4)) :
    separatedBumpSum E a x = 0 := by
  apply Finset.sum_eq_zero
  intro z hz
  rw [smallBallBump_translate, indicator_of_notMem (hx z hz), mul_zero]

theorem separatedBumpSum_norm_le_one {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ)
    (hsep : ∀ z ∈ E, ∀ w ∈ E, z ≠ w → 1 ≤ dist z w)
    (ha : ∀ z ∈ E, ‖a z‖ ≤ 1) (x : Space n) :
    ‖separatedBumpSum E a x‖ ≤ 1 := by
  by_cases hx : ∃ z ∈ E, x ∈ ball z (1 / 4)
  · obtain ⟨z, hz, hxz⟩ := hx
    have he : separatedBumpSum E a x = a z := by
      unfold separatedBumpSum
      rw [Finset.sum_eq_single z]
      · rw [smallBallBump_translate, indicator_of_mem hxz, mul_one]
      · intro w hw hwz
        have hxw : x ∉ ball w (1 / 4) := by
          intro hxw
          have H := dist_triangle w x z
          have hwx : dist w x < 1 / 4 := by simpa only [mem_ball, dist_comm] using hxw
          have hxz' : dist x z < 1 / 4 := hxz
          have HS := hsep w hw z hz hwz
          linarith
        rw [smallBallBump_translate, indicator_of_notMem hxw, mul_zero]
      · exact fun h ↦ (h hz).elim
    rw [he]
    exact ha z hz
  · have hz : ∀ z ∈ E, x ∉ ball z (1 / 4) := by simpa only [not_exists, not_and] using hx
    rw [separatedBumpSum_eq_zero E a x hz, norm_zero]
    norm_num

theorem angularFourier_separatedBumpSum {n : ℕ} (E : Finset (Space n))
    (a : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (separatedBumpSum E a) ξ =
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier (smallBallBump : Space n → ℂ) ξ * finitePhaseSum E a ξ := by
  change OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ ∑ z ∈ E, a z * smallBallBump (x - z)) ξ = _
  rw [angularFourier_sum E _
    (fun z _ ↦ (integrable_smallBallBump_translate z).const_mul (a z))]
  simp_rw [angularFourier_const_mul, angularFourier_translate]
  rw [finitePhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem continuous_finitePhaseSum {n : ℕ} (E : Finset (Space n)) (a : Space n → ℂ) :
    Continuous (finitePhaseSum E a) := by
  unfold finitePhaseSum
  fun_prop

end OAI.Analysis.Fourier.Restriction
