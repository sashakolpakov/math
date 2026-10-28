import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RegularizedBounds

/-! Polar integration on a Euclidean ball, with its exact volume normalization. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem integral_ball_radial {m : ℕ} (hm : 1 ≤ m) (g : ℝ → ℝ) (R : ℝ) :
    (∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) R, g ‖y‖) =
      (m : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        ∫ t in Ioo (0 : ℝ) R, t ^ (m - 1) * g t := by
  let E := EuclideanSpace ℝ (Fin m)
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    change 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin m))
    simpa using (show 0 < m by omega))
  have he := integral_fun_norm_addHaar (volume : Measure E) ((Iio R).indicator g)
  have hspace : (fun y : E => (Iio R).indicator g ‖y‖) = (ball (0 : E) R).indicator (fun y => g ‖y‖) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [hy]
  have hscalar (t : ℝ) : t ^ (m - 1) • (Iio R).indicator g t =
      (Iio R).indicator (fun t => t ^ (m - 1) * g t) t := by
    by_cases ht : t < R <;> simp [ht, smul_eq_mul]
  rw [hspace, integral_indicator measurableSet_ball] at he
  simp only [E, finrank_euclideanSpace_fin, hscalar, nsmul_eq_mul, smul_eq_mul] at he
  rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio] at he
  simpa only [mul_assoc] using he

end OAI.Analysis.PDE.Schauder
