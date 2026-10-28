import OAI.Analysis.Fourier.Radial.ODE
import OAI.Analysis.Fourier.Radial.Tail

/-! Nonzero outgoing and incoming oscillations for the inverse-square
perturbed oscillator, including a quantitative remainder for both the
function and its first derivative. -/

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem oscillator_uniform_bound {u v : ℝ → ℝ} {κ : ℝ}
    (hu : ∀ t, 1 ≤ t → HasDerivAt u (v t) t)
    (hv : ∀ t, 1 ≤ t → HasDerivAt v ((κ / t ^ 2 - 1) * u t) t) :
    ∃ B : ℝ, 0 < B ∧ ∀ t, 1 ≤ t → |u t| ≤ B ∧ |v t| ≤ B := by
  let M := Real.exp |κ| * oscillatorEnergy u v 1
  have hM : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (by
    exact add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨M + 1, by linarith, ?_⟩
  intro t ht
  have H : u t ^ 2 + v t ^ 2 ≤ M := (oscillatorEnergy_bounds hu hv t ht).2
  constructor
  · nlinarith [sq_nonneg (v t), sq_nonneg M, sq_abs (u t), abs_nonneg (u t)]
  · nlinarith [sq_nonneg (u t), sq_nonneg M, sq_abs (v t), abs_nonneg (v t)]

theorem abs_inverseSquare_trig_mul_le {κ t U B h : ℝ}
    (hU : |U| ≤ B) (hh : |h| ≤ 1) :
    |κ / t ^ 2 * U * h| ≤ |κ| * B / t ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg U).trans hU
  rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ (|κ| / t ^ 2) * B * 1 := by gcongr
    _ = _ := by ring

theorem two_trig_errors_le {a b c s D : ℝ} (ha : |a| ≤ D) (hb : |b| ≤ D)
    (hc : |c| ≤ 1) (hs : |s| ≤ 1) : |a * c + b * s| ≤ 2 * D := by
  have hD : 0 ≤ D := (abs_nonneg a).trans ha
  calc
    _ ≤ |a * c| + |b * s| := abs_add_le _ _
    _ = |a| * |c| + |b| * |s| := by rw [abs_mul, abs_mul]
    _ ≤ D * 1 + D * 1 := by gcongr
    _ = _ := by ring

theorem oscillator_asymptotic {u v : ℝ → ℝ} {κ : ℝ}
    (hu : ∀ t, 1 ≤ t → HasDerivAt u (v t) t)
    (hv : ∀ t, 1 ≤ t → HasDerivAt v ((κ / t ^ 2 - 1) * u t) t)
    (hne : 0 < oscillatorEnergy u v 1) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ r, 1 ≤ r →
      |u r - (A * Real.cos r + B * Real.sin r)| ≤ C / r ∧
      |v r - (-A * Real.sin r + B * Real.cos r)| ≤ C / r := by
  obtain ⟨K, hK, hbound⟩ := oscillator_uniform_bound hu hv
  let D := |κ| * K
  have hD : 0 ≤ D := mul_nonneg (abs_nonneg _) hK.le
  have huc : ContinuousOn u (Ici 1) := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hdiv : ContinuousOn (fun t : ℝ => κ / t ^ 2) (Ici 1) :=
    continuousOn_const.div (continuousOn_id.pow 2) (by
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)))
  have hca : ContinuousOn (fun t : ℝ => -κ / t ^ 2 * u t * Real.sin t) (Ici 1) := by
    have H := ((hdiv.neg).mul huc).mul Real.continuous_sin.continuousOn
    change ContinuousOn (fun t : ℝ => -(κ / t ^ 2) * u t * Real.sin t) (Ici 1) at H
    simpa only [neg_div] using H
  have hcb : ContinuousOn (fun t : ℝ => κ / t ^ 2 * u t * Real.cos t) (Ici 1) :=
    (hdiv.mul huc).mul Real.continuous_cos.continuousOn
  obtain ⟨A, hA, hAe⟩ := inverseSquare_derivative_limit hD hca
    (fun t ht => hasDerivAt_outgoingCosine (hu t ht) (hv t ht)) (by
      intro t ht
      simpa only [abs_neg] using abs_inverseSquare_trig_mul_le (κ := -κ)
        (hbound t ht).1 (Real.abs_sin_le_one t))
  obtain ⟨B, hB, hBe⟩ := inverseSquare_derivative_limit hD hcb
    (fun t ht => hasDerivAt_outgoingSine (hu t ht) (hv t ht)) (by
      intro t ht
      exact abs_inverseSquare_trig_mul_le (hbound t ht).1 (Real.abs_cos_le_one t))
  have hn : Real.exp (-|κ|) * oscillatorEnergy u v 1 ≤ A ^ 2 + B ^ 2 := by
    apply ge_of_tendsto ((hA.pow 2).add (hB.pow 2))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [outgoing_energy]
    exact (oscillatorEnergy_bounds hu hv t ht).1
  refine ⟨A, B, 2 * D, by positivity, (mul_pos (Real.exp_pos _) hne).trans_le hn, ?_⟩
  intro r hr
  obtain ⟨hur, hvr⟩ := outgoing_reconstruct u v r
  constructor
  · have he : u r - (A * Real.cos r + B * Real.sin r) =
        (outgoingCosine u v r - A) * Real.cos r + (outgoingSine u v r - B) * Real.sin r := by
      rw [hur]
      ring
    rw [he]
    simpa only [mul_div_assoc] using two_trig_errors_le (hAe r hr) (hBe r hr)
      (Real.abs_cos_le_one r) (Real.abs_sin_le_one r)
  · have he : v r - (-A * Real.sin r + B * Real.cos r) =
        (outgoingCosine u v r - A) * (-Real.sin r) + (outgoingSine u v r - B) * Real.cos r := by
      rw [hvr]
      ring
    rw [he]
    simpa only [mul_div_assoc] using two_trig_errors_le (hAe r hr) (hBe r hr)
      (by simpa only [abs_neg] using Real.abs_sin_le_one r) (Real.abs_cos_le_one r)

end OAI.Analysis.Fourier.Radial
