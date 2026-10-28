import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Unipotent
import OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure

/-! # Unipotent Coset Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentCosetIntegral.Iwasawa

noncomputable section

/-! A single actual unipotent integral coset has volume one in the
iterated additive Haar integral, using the exact GL3 coset equations. -/

open scoped Classical
open _root_.MeasureTheory

variable (q : ℕ) [Fact q.Prime]
  [MeasurableSpace ℚ_[q]] [BorelSpace ℚ_[q]]
  (μ : Measure ℚ_[q]) [μ.IsAddLeftInvariant]
  (hO : MeasurableSet (Unipotent.Iwasawa.padicIntegralSet q)) (hvol : μ (Unipotent.Iwasawa.padicIntegralSet q) = 1)

include hO hvol in
theorem padic_integral_translated_indicator (c : ℚ_[q]) (r : ℂ) :
    (∫ x, if x - c ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0 ∂μ) = r := by
  have hm : μ ((fun x => x - c) ⁻¹' Unipotent.Iwasawa.padicIntegralSet q) = 1 := by
    rw [show (fun x : ℚ_[q] => x - c) = (fun x => -c + x) by funext x; ring]
    rw [measure_preimage_add, hvol]
  have hh := RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.integral_if_mem μ ((fun x : ℚ_[q] => x - c) ⁻¹' Unipotent.Iwasawa.padicIntegralSet q)
    (hO.preimage (measurable_id.sub_const c)) r
  simpa [RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure.complexVolume, measureReal_def, hm] using hh

include hO hvol in
theorem gl3Unipotent_coset_inner_integral (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q)
    (x y z a c : ℚ_[q]) (r : ℂ) :
    (∫ b, if (QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent x y z) :
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) =
        QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent a b c) then r else 0 ∂μ) =
      if a - x ∈ Unipotent.Iwasawa.padicIntegralSet q ∧ c - z ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0 := by
  simp_rw [Unipotent.Iwasawa.gl3Unipotent_coset_iff]
  have he (b : ℚ_[q]) : b - y - x * (c - z) = b - (y + x * (c - z)) := by ring
  simp_rw [he]
  by_cases ha : a - x ∈ Unipotent.Iwasawa.padicIntegralSet q <;> by_cases hc : c - z ∈ Unipotent.Iwasawa.padicIntegralSet q
  · simpa only [ha, hc, true_and, and_true, ite_true] using
      padic_integral_translated_indicator q μ hO hvol (y + x * (c - z)) r
  · simp [ha, hc]
  · simp [ha, hc]
  · simp [ha, hc]

include hO hvol in
theorem gl3Unipotent_coset_middle_integral (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q)
    (x y z a : ℚ_[q]) (r : ℂ) :
    (∫ c, ∫ b, if (QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent x y z) :
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) =
        QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent a b c) then r else 0 ∂μ ∂μ) =
      if a - x ∈ Unipotent.Iwasawa.padicIntegralSet q then r else 0 := by
  simp_rw [gl3Unipotent_coset_inner_integral q μ hO hvol]
  by_cases ha : a - x ∈ Unipotent.Iwasawa.padicIntegralSet q
  · simpa only [ha, true_and, ite_true] using padic_integral_translated_indicator q μ hO hvol z r
  · simp [ha]

include hO hvol in
theorem gl3Unipotent_coset_integral (t : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q) (x y z : ℚ_[q]) (r : ℂ) :
    (∫ a, ∫ c, ∫ b, if (QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent x y z) :
          RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.GL3 q ⧸ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralGL3 q) =
        QuotientGroup.mk (t * Unipotent.Iwasawa.gl3Unipotent a b c) then r else 0 ∂μ ∂μ ∂μ) = r := by
  simp_rw [gl3Unipotent_coset_middle_integral q μ hO hvol]
  exact padic_integral_translated_indicator q μ hO hvol x r

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnipotentCosetIntegral.Iwasawa
