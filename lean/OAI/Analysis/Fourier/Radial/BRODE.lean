import OAI.Analysis.Fourier.Radial.BRIntegration

open OAI.Analysis.Fourier.Wave

/-! The exact radial Bessel equation for the Bochner--Riesz kernel. -/

open _root_.MeasureTheory
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem bochnerRiesz_ball_trace {n : ℕ} {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (x : Space n) :
    ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1) x =
      ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x +
        ∑ j, ballCosineLineSecond (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) x (b j) 0 := by
  let w : Space n → ℝ := OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1
  have hw : Continuous w := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1
  have hi (j : Fin n) : Integrable (fun ξ => -(w ξ * (inner ℝ (b j) ξ) ^ 2) *
      Real.cos (inner ℝ x ξ)) (unitBallVolume n) := integrable_unitBallVolume (by fun_prop)
  change _ = ballCosineKernel w x + ∑ j, ballCosineLineSecond w x (b j) 0
  simp only [ballCosineKernel, ballCosineLineSecond, zero_smul, add_zero]
  rw [← integral_finsetSum _ (fun j _ => hi j), ← integral_add
    (integrable_unitBallVolume (by fun_prop)) (MeasureTheory.integrable_finsetSum _ (fun j _ => hi j))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hs : (∑ j, -(w ξ * (inner ℝ (b j) ξ) ^ 2) * Real.cos (inner ℝ x ξ)) =
      -(w ξ * Real.cos (inner ℝ x ξ)) * ‖ξ‖ ^ 2 := by
    rw [← b.sum_sq_inner_right ξ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs, bochnerRieszSymbol_succ hp]
  change (1 - ‖ξ‖ ^ 2) * w ξ * Real.cos (inner ℝ x ξ) = _
  ring

theorem bochnerRiesz_ball_bessel_equation {n : ℕ} {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n)
    {r : ℝ} (hr : 0 < r) :
    ballCosineLineSecond (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 (b i) r =
      -((n : ℝ) + 2 * p + 1) / r *
          ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 (b i) r -
        ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) (r • b i) := by
  let w : Space n → ℝ := OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1
  have hw : Continuous w := OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1
  have hrot (e : Space n ≃ₗᵢ[ℝ] Space n) (ξ : Space n) : w (e ξ) = w ξ := by
    simp only [w, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, e.norm_map]
  have H := bochnerRiesz_ball_trace hp b (r • b i)
  have heq (j : Fin n) : ballCosineLineSecond w (r • b i) (b j) 0 =
      ballCosineLineDeriv w 0 (b i) r / r +
        if j = i then ballCosineLineSecond w 0 (b i) r -
          ballCosineLineDeriv w 0 (b i) r / r else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [ballCosineLineSecond, zero_smul, add_zero, zero_add, ite_true]
      ring
    · rw [ite_eq_right hji, add_zero]
      exact ballCosine_transverse_second hw hrot (b.norm_eq_one i) (b.norm_eq_one j)
        (b.inner_eq_zero (Ne.symm hji)) hr
  change _ = ballCosineKernel w (r • b i) + ∑ j, ballCosineLineSecond w (r • b i) (b j) 0 at H
  simp_rw [heq] at H
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at H
  have HI := bochnerRiesz_ball_integration_by_parts hp (b.norm_eq_one i) r
  have Hnext : ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol (p + 1) 1) (r • b i) =
      -2 * (p + 1) / r * ballCosineLineDeriv w 0 (b i) r := by
    apply (mul_left_cancel₀ hr.ne')
    rw [HI]
    dsimp only [w]
    field_simp
  rw [Hnext] at H
  change ballCosineLineSecond w 0 (b i) r =
    -((n : ℝ) + 2 * p + 1) / r * ballCosineLineDeriv w 0 (b i) r -
      ballCosineKernel w (r • b i)
  linear_combination -H

theorem hasDerivAt_bochnerRiesz_ball_bessel {n : ℕ} {p : ℝ} (hp : 0 < p)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 (b i))
      (-((n : ℝ) + 2 * p + 1) / r *
          ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) 0 (b i) r -
        ballCosineKernel (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol p 1) (r • b i)) r := by
  rw [← bochnerRiesz_ball_bessel_equation hp b i hr]
  exact hasDerivAt_ballCosineLineDeriv (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hp.le 1) 0 (b i) r

end OAI.Analysis.Fourier.Radial
