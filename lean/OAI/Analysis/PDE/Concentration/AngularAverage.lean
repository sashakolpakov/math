import OAI.Analysis.PDE.Concentration.Cylinder.Calculus
import OAI.Analysis.PDE.Concentration.IntervalAverage

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Laplacian InnerProductSpace
open scoped ContDiff

noncomputable def cylinderAngularAverage (f : CylinderSpace → ℝ) (t r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi), f (cylinderPoint t r θ)

theorem contDiff_cylinderAngularAverage {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderAngularAverage f p.1 p.2) := by
  apply contDiff_intervalAverage (f := fun p : (ℝ × ℝ) × ℝ => f (cylinderPoint p.1.1 p.1.2 p.2))
    (a := 0) (b := 2 * Real.pi) _ (by positivity)
  exact hf.comp (contDiff_cylinderPoint.comp
    ((contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)))

theorem contDiff_cylinder_radius_angle {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (cylinderPoint t p.1 p.2)) :=
  hf.comp (contDiff_cylinderPoint.comp (contDiff_const.prodMk contDiff_id))

theorem contDiff_cylinder_time_angle {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => f (cylinderPoint p.1 r p.2)) :=
  hf.comp (contDiff_cylinderPoint.comp (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)))

theorem cylinder_integral_second_angle {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv (fun s => f (cylinderPoint t r s))) θ) = 0 := by
  let g : ℝ → ℝ := fun θ => f (cylinderPoint t r θ)
  have hg : ContDiff ℝ ∞ g := (contDiff_cylinder_radius_angle hf t).comp (contDiff_const.prodMk contDiff_id)
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hgdd : Continuous (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp hgd).2.continuous
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv g) θ) = 0
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun _ _ => hgd.differentiable (by simp) _) (hgdd.intervalIntegrable _ _)]
  have hd (θ : ℝ) : deriv g θ = fderiv ℝ f (cylinderPoint t r θ) (r • cylinderAngular θ) :=
    ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_cylinderPoint_angle t r θ)).deriv
  rw [hd, hd]
  have he := cylinderPoint_add_two_pi t r 0
  have ha := cylinderAngular_add_two_pi 0
  simp only [zero_add] at he ha
  rw [he, ha, sub_self]

theorem cylinderAngularAverage_first_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : deriv (fun s => cylinderAngularAverage f t s) r =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (fun s => f (cylinderPoint t s θ)) r :=
  deriv_intervalAverage (contDiff_cylinder_radius_angle hf t) (by positivity) r

theorem cylinderAngularAverage_second_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : deriv (deriv (fun s => cylinderAngularAverage f t s)) r =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv (fun s => f (cylinderPoint t s θ))) r :=
  second_deriv_intervalAverage (contDiff_cylinder_radius_angle hf t) (by positivity) r

theorem cylinderAngularAverage_second_time {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : deriv (deriv (fun s => cylinderAngularAverage f s r)) t =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv (fun s => f (cylinderPoint s r θ))) t :=
  second_deriv_intervalAverage (contDiff_cylinder_time_angle hf r) (by positivity) t

private theorem integral_four_sum {A B C D : ℝ → ℝ} {a b : ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    (∫ x in a..b, A x + B x + C x + D x) =
      (∫ x in a..b, A x) + (∫ x in a..b, B x) +
        (∫ x in a..b, C x) + (∫ x in a..b, D x) := by
  have hAB : Continuous (fun x => A x + B x) := hA.add hB
  have hABC : Continuous (fun x => A x + B x + C x) := hAB.add hC
  rw [intervalIntegral.integral_add (hABC.intervalIntegrable a b) (hD.intervalIntegrable a b)]
  rw [intervalIntegral.integral_add (hAB.intervalIntegrable a b) (hC.intervalIntegrable a b)]
  rw [intervalIntegral.integral_add (hA.intervalIntegrable a b) (hB.intervalIntegrable a b)]

theorem continuous_cylinder_first_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : Continuous (fun θ => deriv (fun s => f (cylinderPoint t s θ)) r) :=
  continuous_firstPartial_slice (contDiff_cylinder_radius_angle hf t) r

theorem continuous_cylinder_second_radius {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : Continuous (fun θ => deriv (deriv (fun s => f (cylinderPoint t s θ))) r) :=
  continuous_secondPartial_slice (contDiff_cylinder_radius_angle hf t) r

theorem continuous_cylinder_second_time {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : Continuous (fun θ => deriv (deriv (fun s => f (cylinderPoint s r θ))) t) :=
  continuous_secondPartial_slice (contDiff_cylinder_time_angle hf r) t

theorem continuous_cylinder_second_angle {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) : Continuous (deriv (deriv (fun θ => f (cylinderPoint t r θ)))) := by
  have hang : ContDiff ℝ ∞ (fun θ => f (cylinderPoint t r θ)) :=
    (contDiff_cylinder_radius_angle hf t).comp (contDiff_const.prodMk contDiff_id)
  exact (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hang).2).2.continuous

private theorem integrated_cylinder_laplacian {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) (hr : r ≠ 0) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv (fun s => f (cylinderPoint t s θ))) r) +
      (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (fun s => f (cylinderPoint t s θ)) r) / r +
      (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (deriv (fun s => f (cylinderPoint s r θ))) t) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Δ f (cylinderPoint t r θ) := by
  have hrad1 := continuous_cylinder_first_radius hf t r
  have hrad2 := continuous_cylinder_second_radius hf t r
  have htime2 := continuous_cylinder_second_time hf t r
  have hang2 := continuous_cylinder_second_angle hf t r
  have he : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      deriv (deriv (fun s => f (cylinderPoint t s θ))) r +
        deriv (fun s => f (cylinderPoint t s θ)) r / r +
        deriv (deriv (fun s => f (cylinderPoint t r s))) θ / r ^ 2 +
        deriv (deriv (fun s => f (cylinderPoint s r θ))) t) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Δ f (cylinderPoint t r θ) :=
    intervalIntegral.integral_congr (fun θ _ => cylinder_laplacian_identity
      (hf.of_le (by simp)) t r θ hr)
  rw [integral_four_sum hrad2 (hrad1.div_const r) (hang2.div_const (r ^ 2)) htime2,
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    cylinder_integral_second_angle hf, zero_div, add_zero] at he
  exact he

/-- Exact angular averaging of the three-dimensional Laplacian. -/
theorem cylinderAngularAverage_laplacian {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (t r : ℝ) (hr : r ≠ 0) :
    deriv (deriv (fun s => cylinderAngularAverage f t s)) r +
      deriv (fun s => cylinderAngularAverage f t s) r / r +
      deriv (deriv (fun s => cylinderAngularAverage f s r)) t =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Δ f (cylinderPoint t r θ) := by
  rw [cylinderAngularAverage_second_radius hf, cylinderAngularAverage_first_radius hf,
    cylinderAngularAverage_second_time hf]
  exact integrated_cylinder_laplacian hf t r hr

end OAI.Analysis.PDE.Concentration
