import OAI.Analysis.PDE.Concentration.AngularAverage

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set

noncomputable def cylinderCartesianEquiv : CylinderSpace ≃ᵐ ℝ × ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))))

theorem cylinderCartesianEquiv_apply (x : CylinderSpace) :
    cylinderCartesianEquiv x = (x 0, x 1, x 2) := by
  rfl

theorem cylinderCartesianEquiv_point (t r θ : ℝ) :
    cylinderCartesianEquiv (cylinderPoint t r θ) = (t, r * Real.cos θ, r * Real.sin θ) := by
  rw [cylinderCartesianEquiv_apply]
  simp [cylinderPoint, cylinderRadial, cylinderAxis, EuclideanSpace.basisFun_apply]

theorem cylinderCartesianEquiv_measurePreserving : MeasurePreserving cylinderCartesianEquiv := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))
  exact h3.comp (h2.comp h1)

theorem cylinderAngularAverage_eq_centered (f : CylinderSpace → ℝ) (t r : ℝ) :
    cylinderAngularAverage f t r = ∫ θ in (-Real.pi)..Real.pi, f (cylinderPoint t r θ) := by
  have hp : Function.Periodic (fun θ => f (cylinderPoint t r θ)) (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [cylinderPoint_add_two_pi]
  have he := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have he' : -Real.pi + 2 * Real.pi = Real.pi := by ring
  simpa only [zero_add, he', cylinderAngularAverage] using he

theorem cylinderCartesianEquiv_symm_apply (p : ℝ × ℝ × ℝ) :
    cylinderCartesianEquiv.symm p = p.1 • cylinderAxis 0 +
      p.2.1 • cylinderAxis 1 + p.2.2 • cylinderAxis 2 := by
  apply cylinderCartesianEquiv.injective
  simp [cylinderCartesianEquiv_apply, cylinderAxis, EuclideanSpace.basisFun_apply]

theorem continuous_cylinderCartesianEquiv_symm : Continuous cylinderCartesianEquiv.symm := by
  simp_rw [show (fun p => cylinderCartesianEquiv.symm p) =
      (fun p : ℝ × ℝ × ℝ => p.1 • cylinderAxis 0 + p.2.1 • cylinderAxis 1 + p.2.2 • cylinderAxis 2) by
    funext p; exact cylinderCartesianEquiv_symm_apply p]
  fun_prop

noncomputable def cylinderComplexEquiv : CylinderSpace ≃ᵐ ℝ × ℂ :=
  cylinderCartesianEquiv.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivRealProd.symm)

theorem cylinderComplexEquiv_apply (x : CylinderSpace) :
    cylinderComplexEquiv x = (x 0, (x 1 : ℂ) + (x 2 : ℂ) * Complex.I) := by
  apply Prod.ext
  · rfl
  · apply Complex.ext
    · change x 1 = ((x 1 : ℂ) + (x 2 : ℂ) * Complex.I).re
      simp
    · change x 2 = ((x 1 : ℂ) + (x 2 : ℂ) * Complex.I).im
      simp

theorem cylinderComplexEquiv_measurePreserving : MeasurePreserving cylinderComplexEquiv :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod Complex.volume_preserving_equiv_real_prod.symm).comp
    cylinderCartesianEquiv_measurePreserving

theorem cylinderComplexEquiv_symm_apply (t : ℝ) (z : ℂ) :
    cylinderComplexEquiv.symm (t, z) = cylinderCartesianEquiv.symm (t, z.re, z.im) := rfl

theorem continuous_cylinderComplexEquiv_symm : Continuous cylinderComplexEquiv.symm :=
  continuous_cylinderCartesianEquiv_symm.comp
    (continuous_fst.prodMk ((Complex.continuous_re.comp continuous_snd).prodMk
      (Complex.continuous_im.comp continuous_snd)))

theorem cylinderComplexEquiv_symm_polar (t r θ : ℝ) :
    cylinderComplexEquiv.symm (t, Complex.polarCoord.symm (r, θ)) = cylinderPoint t r θ := by
  rw [cylinderComplexEquiv_symm_apply]
  apply cylinderCartesianEquiv.injective
  simp [cylinderCartesianEquiv_point, Complex.polarCoord_symm_apply,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cylinderComplexEquiv_point (t r θ : ℝ) :
    cylinderComplexEquiv (cylinderPoint t r θ) = (t, Complex.polarCoord.symm (r, θ)) := by
  rw [← cylinderComplexEquiv_symm_polar t r θ, MeasurableEquiv.apply_symm_apply]

theorem cylinderComplexCoordinate_dist_le (x y : CylinderSpace) :
    dist (cylinderComplexEquiv x).2 (cylinderComplexEquiv y).2 ≤ 2 * dist x y := by
  have h := Complex.norm_le_abs_re_add_abs_im ((cylinderComplexEquiv x).2 - (cylinderComplexEquiv y).2)
  have h1 := PiLp.norm_apply_le (x - y) (1 : Fin 3)
  have h2 := PiLp.norm_apply_le (x - y) (2 : Fin 3)
  simp only [cylinderComplexEquiv_apply, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero,
    add_zero, zero_add, mul_one, PiLp.sub_apply, Real.norm_eq_abs] at h h1 h2
  rw [dist_eq_norm, dist_eq_norm, cylinderComplexEquiv_apply, cylinderComplexEquiv_apply]
  linarith

end OAI.Analysis.PDE.Concentration
