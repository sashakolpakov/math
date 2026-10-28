import Mathlib

/-! Differentiating positive-part powers across their support boundary. -/

open Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

def positivePower (p x : ℝ) : ℝ := (max x 0) ^ p

theorem continuous_positivePower {p : ℝ} (hp : 0 ≤ p) : Continuous (positivePower p) := by
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr hp)

theorem hasDerivAt_positivePower_of_ne {p x : ℝ} (hp : 1 < p) (hx : x ≠ 0) :
    HasDerivAt (positivePower p) (p * positivePower (p - 1) x) x := by
  rcases lt_or_gt_of_ne hx with hn | hn
  · have H : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (p * positivePower (p - 1) x) x := by
      simpa only [positivePower, max_eq_right hn.le, Real.zero_rpow (by linarith : p - 1 ≠ 0),
        mul_zero] using hasDerivAt_const x (0 : ℝ)
    apply H.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hn] with y hy
    simp only [positivePower, max_eq_right (le_of_lt hy), Real.zero_rpow (by linarith : p ≠ 0)]
  · have H : HasDerivAt (fun y : ℝ => y ^ p) (p * positivePower (p - 1) x) x := by
      simpa only [positivePower, max_eq_left hn.le] using
        (Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inl hx))
    apply H.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hn] with y hy
    simp only [positivePower, max_eq_left (le_of_lt hy)]

theorem hasDerivAt_positivePower {p : ℝ} (hp : 1 < p) (x : ℝ) :
    HasDerivAt (positivePower p) (p * positivePower (p - 1) x) x := by
  by_cases hx : x = 0
  · subst x
    apply hasDerivAt_of_hasDerivAt_of_ne (fun y hy => hasDerivAt_positivePower_of_ne hp hy)
    · exact (continuous_positivePower (by linarith)).continuousAt
    · exact (continuous_const.mul (continuous_positivePower (by linarith))).continuousAt
  · exact hasDerivAt_positivePower_of_ne hp hx

theorem contDiff_positivePower {p : ℝ} (hp : 1 < p) :
    ContDiff ℝ 1 (positivePower p) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_positivePower hp x).differentiableAt, ?_⟩
  have hd : deriv (positivePower p) = fun x => p * positivePower (p - 1) x :=
    funext (fun x => (hasDerivAt_positivePower hp x).deriv)
  rw [hd]
  exact continuous_const.mul (continuous_positivePower (by linarith))

end OAI.Analysis.Fourier.Radial
