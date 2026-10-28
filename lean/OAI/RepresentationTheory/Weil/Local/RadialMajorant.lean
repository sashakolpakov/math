import OAI.RepresentationTheory.Weil.Local.PlanarRadialIntegral

/-! # Radial Majorant -/

namespace OAI.RepresentationTheory.Weil.Local.RadialMajorant.Construction

noncomputable section

/-! An integrable radial inverse-square majorant and its exact integral. -/

open _root_.MeasureTheory Set

theorem planarRadial_integral_real (f : ℝ → ℝ) :
    (∫ z : ℝ × ℝ, f (PlanarRadialCompact.Construction.planarRadiusSquared z)) = Real.pi * ∫ t in Ioi (0 : ℝ), f t := by
  have hc := PlanarRadialIntegral.Construction.planarRadial_integral (fun t => (f t : ℂ))
  change (∫ z : ℝ × ℝ, (f (PlanarRadialCompact.Construction.planarRadiusSquared z) : ℂ)) =
    (Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ), (f t : ℂ) at hc
  rw [integral_complex_ofReal, integral_complex_ofReal] at hc
  exact_mod_cast hc

theorem planarRadial_integrable_real (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ))) :
    Integrable (fun z : ℝ × ℝ => f (PlanarRadialCompact.Construction.planarRadiusSquared z)) := by
  have hi := (PlanarRadialIntegral.Construction.planarRadial_integrable (fun t => (f t : ℂ)) hf.ofReal).re
  change Integrable (fun z : ℝ × ℝ => (f (PlanarRadialCompact.Construction.planarRadiusSquared z) : ℂ).re) at hi
  simpa only [Complex.ofReal_re] using hi

theorem real_rpow_negative_two (t : ℝ) : t ^ (-2 : ℝ) = 1 / t ^ 2 := by
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_two, one_div, inv_pow]

theorem inverse_square_tail_integrable (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ici R) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have hi := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hR
  simpa only [real_rpow_negative_two] using hi

theorem inverse_square_tail_integral (R : ℝ) (hR : 0 < R) :
    (∫ t in Ici R, (1 : ℝ) / t ^ 2) = 1 / R := by
  rw [integral_Ici_eq_integral_Ioi]
  have hi := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hR
  norm_num only [real_rpow_negative_two, show (-2 : ℝ) + 1 = -1 by norm_num,
    Real.rpow_neg_one, neg_div_neg_eq, div_one] at hi
  simpa only [one_div] using hi

def radialInverseSquareMajorant (R C t : ℝ) : ℝ := (Ici R).indicator (fun t => C / t ^ 2) t

theorem radialInverseSquareMajorant_integrable (R C : ℝ) (hR : 0 < R) :
    Integrable (radialInverseSquareMajorant R C) := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  simpa only [mul_one_div] using! (inverse_square_tail_integrable R hR).const_mul C

theorem radialInverseSquareMajorant_nonneg (R C t : ℝ) (hC : 0 ≤ C) :
    0 ≤ radialInverseSquareMajorant R C t := by
  apply indicator_nonneg
  intro x _
  exact div_nonneg hC (sq_nonneg x)

theorem radialInverseSquareMajorant_integral (R C : ℝ) (hR : 0 < R) :
    (∫ t in Ioi (0 : ℝ), radialInverseSquareMajorant R C t) = C / R := by
  change (∫ t in Ioi (0 : ℝ), (Ici R).indicator (fun t => C / t ^ 2) t) = C / R
  rw [integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hs : Ici R ∩ Ioi (0 : ℝ) = Ici R :=
    inter_eq_left.mpr (fun _ ht => hR.trans_le ht)
  rw [hs]
  have heq : (fun t : ℝ => C / t ^ 2) = fun t => C * (1 / t ^ 2) := by funext t; ring
  rw [heq, integral_const_mul, inverse_square_tail_integral R hR]
  ring

theorem planar_radialInverseSquareMajorant_integrable (R C : ℝ) (hR : 0 < R) :
    Integrable (fun z : ℝ × ℝ => radialInverseSquareMajorant R C (PlanarRadialCompact.Construction.planarRadiusSquared z)) :=
  planarRadial_integrable_real _ (radialInverseSquareMajorant_integrable R C hR).integrableOn

theorem planar_radialInverseSquareMajorant_integral (R C : ℝ) (hR : 0 < R) :
    (∫ z : ℝ × ℝ, radialInverseSquareMajorant R C (PlanarRadialCompact.Construction.planarRadiusSquared z)) = Real.pi * C / R := by
  rw [planarRadial_integral_real, radialInverseSquareMajorant_integral R C hR]
  ring

end

end OAI.RepresentationTheory.Weil.Local.RadialMajorant.Construction
