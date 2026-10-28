import OAI.Geometry.Nikodym.Jacobi.RadialMetric

noncomputable section
namespace OAI.Geometry.Nikodym

open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def projectiveRadialMap (κ : ℝ) (x : E) : E :=
  (curvatureTan κ ‖x‖ / ‖x‖) • x

theorem projectiveRadialMap_norm_sq (κ : ℝ) (x : E) :
    ‖projectiveRadialMap κ x‖^2 = (curvatureTan κ ‖x‖)^2 := by
  by_cases hx : x = 0
  · subst x
    simp [projectiveRadialMap]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [projectiveRadialMap,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow]
  field_simp

theorem beltramiDenominator_projectiveRadialMap (κ : ℝ) (x : E)
    (hc : curvatureCos κ ‖x‖ ≠ 0) :
    beltramiDenominator κ (projectiveRadialMap κ x) = 1/(curvatureCos κ ‖x‖)^2 := by
  rw [beltramiDenominator,projectiveRadialMap_norm_sq]
  exact curvatureTan_denominator κ ‖x‖ hc

theorem contDiffAt_projectiveRadialMap (κ : ℝ) {x : E} (hx : x ≠ 0)
    (hc : curvatureCos κ ‖x‖ ≠ 0) :
    ContDiffAt ℝ ∞ (projectiveRadialMap κ) x := by
  have hn : ContDiffAt ℝ ∞ (fun x : E => ‖x‖) x := contDiffAt_norm ℝ hx
  exact (((contDiffAt_curvatureTan κ ‖x‖ hc).comp x hn).div hn
    (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

private theorem norm_curve_derivative {γ : ℝ → E} {t : ℝ} {w : E}
    (hγ : HasDerivAt γ w t) (hx : γ t ≠ 0) :
    HasDerivAt (fun s => ‖γ s‖) (⟪γ t,w⟫ / ‖γ t‖) t := by
  have hd := hγ.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  convert hd using 1
  · ext s
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · rw [Real.sqrt_sq (norm_nonneg _)]
    ring

theorem hasDerivAt_projectiveRadialMap {κ r t : ℝ} {e : E}
    (hr : 0 < r) (he : ‖e‖ = 1) (hc : curvatureCos κ r ≠ 0)
    {γ : ℝ → E} {w : E} (hγ : HasDerivAt γ w t) (hγt : γ t = r • e) :
    HasDerivAt (fun s => projectiveRadialMap κ (γ s))
      (projectiveRadialDerivative κ r e w) t := by
  have hnorm : ‖γ t‖ = r := by simp [hγt,norm_smul,he,Real.norm_eq_abs,abs_of_pos hr]
  have hnormr : ‖r • e‖ = r := by rw [← hγt,hnorm]
  have hne : γ t ≠ 0 := by intro hz; rw [hz,norm_zero] at hnorm; linarith
  have hn : HasDerivAt (fun s => ‖γ s‖) ⟪e,w⟫ t := by
    convert norm_curve_derivative hγ hne using 1
    rw [hγt,real_inner_smul_left,show ‖r • e‖ = r by rw [← hγt,hnorm]]
    field_simp
  have htan : HasDerivAt (fun s => curvatureTan κ ‖γ s‖)
      ((1/(curvatureCos κ r)^2)*⟪e,w⟫) t := by
    simpa only [hnorm] using! (hasDerivAt_curvatureTan κ ‖γ t‖ (by rwa [hnorm])).comp t hn
  have hd := ((htan.div hn (by rw [hnorm]; exact hr.ne')).smul hγ)
  convert hd using 1
  · rfl
  · simp only [projectiveRadialDerivative,Pi.div_apply,hγt,hnormr]
    have hcoef : (1/(curvatureCos κ r)^2)*⟪e,w⟫ - (curvatureTan κ r/r)*⟪e,w⟫ =
        (((1/(curvatureCos κ r)^2)*⟪e,w⟫*r - curvatureTan κ r*⟪e,w⟫)/r^2)*r := by
      field_simp
    calc
      _ = ((1/(curvatureCos κ r)^2)*⟪e,w⟫ - (curvatureTan κ r/r)*⟪e,w⟫) • e +
          (curvatureTan κ r/r) • w := by module
      _ = _ := by rw [hcoef]; module

theorem fderiv_projectiveRadialMap (κ r : ℝ) {e : E}
    (hr : 0 < r) (he : ‖e‖ = 1) (hc : curvatureCos κ r ≠ 0) (w : E) :
    fderiv ℝ (projectiveRadialMap κ) (r • e) w = projectiveRadialDerivative κ r e w := by
  have hnorm : ‖r • e‖ = r := by simp [norm_smul,he,Real.norm_eq_abs,abs_of_pos hr]
  have hne : r • e ≠ 0 := by intro hz; rw [hz,norm_zero] at hnorm; linarith
  have hf := (contDiffAt_projectiveRadialMap κ hne (by rwa [hnorm])).differentiableAt (by simp)
  have hl : HasDerivAt (fun t : ℝ => r • e + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const w).const_add (r • e)
  have h₁ := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have h₂ := hasDerivAt_projectiveRadialMap hr he hc hl (by simp)
  simpa only [zero_smul,add_zero] using h₁.unique h₂

theorem projectiveRadialMap_pullback_metric (κ r : ℝ) {e : E}
    (hr : 0 < r) (he : ‖e‖ = 1) (hc : curvatureCos κ r ≠ 0) (w z : E) :
    beltramiMetric κ (projectiveRadialMap κ (r • e))
      (fderiv ℝ (projectiveRadialMap κ) (r • e) w)
      (fderiv ℝ (projectiveRadialMap κ) (r • e) z) = normalRadialMetric κ r e w z := by
  have hm : projectiveRadialMap κ (r • e) = curvatureTan κ r • e := by
    simp only [projectiveRadialMap,norm_smul,he,Real.norm_eq_abs,abs_of_pos hr,mul_one,smul_smul]
    congr 1
    field_simp
  rw [hm,fderiv_projectiveRadialMap κ r hr he hc w,fderiv_projectiveRadialMap κ r hr he hc z]
  exact beltramiMetric_projectiveRadialDerivative κ r he hr.ne' hc w z

end OAI.Geometry.Nikodym
