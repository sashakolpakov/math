import OAI.Analysis.PDE.Schauder.Calculus.Schauder.GradientBound

/-! Uniform zeroth and first derivative bounds for compact Newtonian data. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem newtonianPotential_bound {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Integrable f) {U I : ℝ}
    (_ : 0 ≤ U) (hub : ∀ y, |f y| ≤ U) (hI : (∫ y, |f y|) ≤ I)
    (x : EuclideanSpace ℝ (Fin m)) :
    |newtonianPotential f x| ≤ U * rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2 + I := by
  let N : EuclideanSpace ℝ (Fin m) → ℝ :=
    (ball 0 1).indicator (fun y => ‖y‖ ^ (2 - (m : ℝ)))
  have hNi : Integrable N := by
    apply IntegrableOn.integrable_indicator _ measurableSet_ball
    simpa only [finrank_euclideanSpace_fin] using
      (integrableOn_riesz_majorant (volume : Measure (EuclideanSpace ℝ (Fin m)))
        (by simpa using (show 1 ≤ m by omega)) (by norm_num : (0 : ℝ) < 2) 1)
  have hmajor : Integrable (fun y => U * N y + |f (x - y)|) :=
    (hNi.const_mul U).add (hf.comp_sub_left x).norm
  have hb : ∀ᵐ y, ‖newtonianKernel m y * f (x - y)‖ ≤ U * N y + |f (x - y)| := by
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, newtonianKernel_eq_norm_rpow,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin m)) 1
    · have hN : N y = ‖y‖ ^ (2 - (m : ℝ)) := Set.indicator_of_mem hy _
      rw [hN]
      have he := mul_le_mul_of_nonneg_left (hub (x - y)) (Real.rpow_nonneg (norm_nonneg y) (2 - (m : ℝ)))
      nlinarith [abs_nonneg (f (x - y))]
    · have hN : N y = 0 := Set.indicator_of_notMem hy _
      rw [hN, mul_zero, zero_add]
      have hn : 1 ≤ ‖y‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hy
      have he : ‖y‖ ^ (2 - (m : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn (by exact_mod_cast (show (2 : ℤ) - m ≤ 0 by omega))
      simpa using mul_le_mul_of_nonneg_right he (abs_nonneg (f (x - y)))
  have hb' := norm_integral_le_of_norm_le hmajor hb
  have hNint : (∫ y, N y) = rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2 := by
    rw [show N = (ball (0 : EuclideanSpace ℝ (Fin m)) 1).indicator (fun y => ‖y‖ ^ (2 - (m : ℝ))) from rfl,
      integral_indicator measurableSet_ball]
    simpa only [finrank_euclideanSpace_fin, Real.one_rpow, one_mul] using
      (integral_riesz_majorant_ball (volume : Measure (EuclideanSpace ℝ (Fin m))) 2 (by norm_num : (0 : ℝ) < 1))
  have hfint : (∫ y, |f (x - y)|) = ∫ y, |f y| := integral_sub_left_eq_self (fun y => |f y|) volume x
  have hfi : Integrable (fun y => |f (x - y)|) := (hf.comp_sub_left x).norm
  rw [integral_add (hNi.const_mul U) hfi, integral_const_mul, hNint, hfint] at hb'
  change ‖∫ y, newtonianKernel m y * f (x - y)‖ ≤ _
  exact hb'.trans (add_le_add le_rfl hI)

theorem newtonianPotential_sub {m : ℕ} (hm : 1 ≤ m)
    (f g : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    newtonianPotential (fun x => f x - g x) = fun x => newtonianPotential f x - newtonianPotential g x := by
  funext x
  unfold newtonianPotential
  simp_rw [mul_sub]
  exact integral_sub (newtonianPotential_integrable hm f hf hfc x)
    (newtonianPotential_integrable hm g hg hgc x)

theorem newtonianPotential_gradient_bound {m : ℕ} (hm : 2 ≤ m) {α : ℝ} (hα : 0 < α) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ H U I, 0 ≤ H → 0 ≤ U → 0 ≤ I →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, |f x| ≤ U) → (∫ y, |f y|) ≤ I →
      ∀ x, ‖fderiv ℝ (newtonianPotential f) x‖ ≤ C * (H + U + I) := by
  obtain ⟨C, hC, hc⟩ := newtonianPotential_hessian_bound hm hα
  let B := rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) 2
  have hB : 0 ≤ B := rieszBallMass_nonneg volume 2
  refine ⟨2 * (B + 1) + C, by positivity, ?_⟩
  intro f hf hfc H U I hH hU hI hh hu hi x
  have hpot := newtonianPotential_bound hm f (hf.continuous.integrable_of_hasCompactSupport hfc) hU hu hi
  have hHess := hc f hf hfc H U I hH hU hI hh hu hi
  have hgrad := gradient_bound_of_function_hessian_bound (newtonianPotential f)
    (contDiff_newtonianPotential (show 1 ≤ m by omega) f hf hfc)
    (by positivity : 0 ≤ U * B + I) (by positivity : 0 ≤ C * (H + U + I)) hpot hHess x
  exact hgrad.trans (by nlinarith [mul_nonneg hB hH, mul_nonneg hB hI])

end OAI.Analysis.PDE.Schauder
