import OAI.RepresentationTheory.Weil.Local.PlanarRadialCompact
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Planar Radial Integral -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarRadialIntegral.Construction

noncomputable section

/-! Reduction of radial planar integrals to integrals in the squared radius. -/

open _root_.MeasureTheory Measure Set Real

theorem planarRadiusSquared_polar (p : ℝ × ℝ) :
    PlanarRadialCompact.Construction.planarRadiusSquared (polarCoord.symm p) = p.1 ^ 2 := by
  change (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2
  calc
    _ = p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem planarRadial_integral (F : ℝ → ℂ) :
    (∫ z, PlanarRadialCompact.Construction.planarRadial F z) = (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ), F t := by
  have hsub : (2 : ℂ) * (∫ r in Ioi (0 : ℝ), (r : ℂ) * F (r ^ 2)) =
      ∫ t in Ioi (0 : ℝ), F t := by
    have ht := integral_comp_rpow_Ioi_of_pos (g := F) (p := 2) (by norm_num)
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two] at ht
    rw [← integral_const_mul]
    convert! ht using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by simp [Complex.real_smul, mul_assoc]
  calc
    _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, (p.1 : ℂ) * F (p.1 ^ 2) := by
      rw [← integral_comp_polarCoord_symm, polarCoord_target]
      simp only [PlanarRadialCompact.Construction.planarRadial, planarRadiusSquared_polar, Complex.real_smul]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * F (r ^ 2)) *
        ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp only [mul_one]
    _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * F (r ^ 2)) * (2 * Real.pi) := by
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
        volume_real_Ioo_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
        sub_neg_eq_add, ← two_mul, Complex.real_smul, mul_one, Complex.ofReal_mul,
        Complex.ofReal_ofNat]
    _ = (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ), F t := by rw [← hsub]; ring

theorem planarRadial_integrable (F : ℝ → ℂ) (hF : IntegrableOn F (Ioi (0 : ℝ))) :
    Integrable (PlanarRadialCompact.Construction.planarRadial F) := by
  have hr : IntegrableOn (fun r : ℝ => (r : ℂ) * F (r ^ 2)) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_Ioi_comp_rpow_iff' F (p := 2) (by norm_num)).mpr hF
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      Complex.real_smul] at h
    exact h
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hprod := hr.mul_prod h1
  rw [Measure.prod_restrict] at hprod
  change IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (p.1 ^ 2) * 1)
    (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) at hprod
  have hpolar : IntegrableOn (fun p : ℝ × ℝ => |p.1| • PlanarRadialCompact.Construction.planarRadial F (polarCoord.symm p))
      polarCoord.target := by
    apply hprod.congr_fun _ polarCoord.open_target.measurableSet
    intro p hp
    dsimp only
    rw [PlanarRadialCompact.Construction.planarRadial, planarRadiusSquared_polar, abs_of_pos (show 0 < p.1 from hp.1),
      Complex.real_smul, mul_one]
  have hJ := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn (PlanarRadialCompact.Construction.planarRadial F)
  rw [polarCoord.symm_image_target_eq_source] at hJ
  simp only [det_fderivPolarCoordSymm] at hJ
  have hsource := hJ.mpr hpolar
  have hglobal := (integrableOn_congr_set_ae polarCoord_source_ae_eq_univ).mp hsource
  simpa only [integrableOn_univ] using hglobal

end

end OAI.RepresentationTheory.Weil.Local.PlanarRadialIntegral.Construction
