import Mathlib

/-! # Analytic Series -/

namespace OAI.RepresentationTheory.Theta.AnalyticSeries

noncomputable section

/-! A local power-series criterion for the exponential sums used in CompletedTheta. -/

open scoped BigOperators _root_.Topology NNReal ENNReal
open Filter Set _root_.Metric

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exponential_coefficient_bound (b : ℂ) (l : E →L[ℂ] ℂ)
    (r : ℝ≥0) (n : ℕ) :
    ‖(b • (NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap l) n‖ *
      (r : ℝ) ^ n ≤ ‖b‖ * ((‖l‖ * (r : ℝ)) ^ n / (n.factorial : ℝ)) := by
  have he : ‖NormedSpace.expSeries ℂ ℂ n‖ = (n.factorial : ℝ)⁻¹ := by
    simp [NormedSpace.expSeries, norm_smul,
      ContinuousMultilinearMap.norm_mkPiAlgebraFin]
  have hc := (NormedSpace.expSeries ℂ ℂ).norm_compContinuousLinearMap_le l n
  rw [he] at hc
  calc
    ‖(b • (NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap l) n‖ * (r : ℝ) ^ n =
        (‖b‖ * ‖(NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap l n‖) *
          (r : ℝ) ^ n := by simp [norm_smul]
    _ ≤ (‖b‖ * ((n.factorial : ℝ)⁻¹ * ‖l‖ ^ n)) * (r : ℝ) ^ n := by
      gcongr
    _ = _ := by simp only [mul_pow, div_eq_mul_inv]; ring

theorem analyticAt_sum_of_coefficients
    (f : I → E → ℂ) (p : I → FormalMultilinearSeries ℂ E ℂ)
    (x : E) (r : ℝ≥0) (hr : 0 < r)
    (hnorm : Summable (fun q : I × ℕ => ‖p q.1 q.2‖ * (r : ℝ) ^ q.2))
    (hsum : ∀ i y, HasSum (fun n => p i n (fun _ => y)) (f i (x + y))) :
    AnalyticAt ℂ (fun y => ∑' i, f i y) x := by
  have hpn (n : ℕ) : Summable (fun i => ‖p i n‖) := by
    apply (summable_mul_right_iff (pow_ne_zero n (ne_of_gt (show 0 < (r : ℝ) from hr)))).mp
    exact hnorm.prod_symm.prod_factor n
  let P : FormalMultilinearSeries ℂ E ℂ := fun n => ∑' i, p i n
  have hP : Summable (fun n => ‖P n‖ * (r : ℝ) ^ n) := by
    apply hnorm.prod_symm.prod.of_nonneg_of_le (fun n => by positivity)
    intro n
    calc
      ‖P n‖ * (r : ℝ) ^ n ≤ (∑' i, ‖p i n‖) * (r : ℝ) ^ n := by
        exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (hpn n)) (by positivity)
      _ = ∑' i, ‖p i n‖ * (r : ℝ) ^ n := (tsum_mul_right).symm
  refine ⟨P, (⟨P.le_radius_of_summable hP, ENNReal.coe_pos.mpr hr, ?_⟩ :
    HasFPowerSeriesOnBall _ P x (r : ℝ≥0∞)).hasFPowerSeriesAt⟩
  intro y hy
  have hyr : ‖y‖ ≤ (r : ℝ) := by
    exact_mod_cast (mem_eball_zero_iff.mp hy).le
  have hyeval : Summable (fun q : I × ℕ => p q.1 q.2 (fun _ => y)) := by
    apply Summable.of_norm_bounded hnorm
    intro q
    calc
      ‖p q.1 q.2 (fun _ => y)‖ ≤ ‖p q.1 q.2‖ * ‖y‖ ^ q.2 := by
        simpa using (p q.1 q.2).le_opNorm (fun _ => y)
      _ ≤ ‖p q.1 q.2‖ * (r : ℝ) ^ q.2 := by gcongr
  have heq : (fun n => P n (fun _ => y)) =
      fun n => ∑' i, p i n (fun _ => y) := by
    funext n
    exact ContinuousMultilinearMap.tsum_eval (hpn n).of_norm _
  rw [heq]
  convert hyeval.prod_symm.prod.hasSum using 1
  · rfl
  · symm
    rw [hyeval.tsum_comm]
    exact tsum_congr (fun i => (hsum i y).tsum_eq)

theorem analyticAt_exponential_sum
    (a : I → ℂ) (l : I → E →L[ℂ] ℂ) (x : E)
    (r : ℝ≥0) (hr : 0 < r)
    (hs : Summable (fun i =>
      ‖a i * Complex.exp (l i x)‖ * Real.exp (‖l i‖ * (r : ℝ)))) :
    AnalyticAt ℂ (fun y => ∑' i, a i * Complex.exp (l i y)) x := by
  let b : I → ℂ := fun i => a i * Complex.exp (l i x)
  let p : I → FormalMultilinearSeries ℂ E ℂ := fun i =>
    b i • (NormedSpace.expSeries ℂ ℂ).compContinuousLinearMap (l i)
  let u : I × ℕ → ℝ := fun q =>
    ‖b q.1‖ * ((‖l q.1‖ * (r : ℝ)) ^ q.2 / (q.2.factorial : ℝ))
  have hu : Summable u := by
    apply (summable_prod_of_nonneg (fun q => by dsimp [u]; positivity)).mpr
    constructor
    · intro i
      exact (NormedSpace.expSeries_div_summable (‖l i‖ * (r : ℝ))).mul_left ‖b i‖
    · simpa only [u, tsum_mul_left, ← Real.exp_eq_exp_ℝ,
        (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq] using hs
  have hp_bound (i : I) (n : ℕ) :
      ‖p i n‖ * (r : ℝ) ^ n ≤ u (i, n) := by
    exact exponential_coefficient_bound (b i) (l i) r n
  have hnorm : Summable (fun q : I × ℕ => ‖p q.1 q.2‖ * (r : ℝ) ^ q.2) :=
    hu.of_nonneg_of_le (fun q => by positivity) (fun q => hp_bound q.1 q.2)
  apply analyticAt_sum_of_coefficients
    (fun i y => a i * Complex.exp (l i y)) p x r hr hnorm
  intro i y
  change HasSum
    (fun n => b i * (NormedSpace.expSeries ℂ ℂ n (fun _ => l i y)))
    (a i * Complex.exp (l i (x + y)))
  rw [show a i * Complex.exp (l i (x + y)) = b i * NormedSpace.exp (l i y) by
    simp only [b, map_add, Complex.exp_add, ← Complex.exp_eq_exp_ℂ, mul_assoc]]
  exact (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (l i y)).mul_left (b i)

end

end OAI.RepresentationTheory.Theta.AnalyticSeries
