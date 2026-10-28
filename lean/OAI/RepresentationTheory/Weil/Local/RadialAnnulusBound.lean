import OAI.RepresentationTheory.Weil.Local.RadialAnnulusWeight
import OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound

/-! # Radial Annulus Bound -/

namespace OAI.RepresentationTheory.Weil.Local.RadialAnnulusBound.Construction

noncomputable section

/-! Annular Laplacian bounds uniform in both the damping and the outer cutoff. -/

theorem radialTailWeight_abs_le (s ε R t : ℝ) (hε : 0 ≤ ε) (ht : 0 < t) :
    |RadialTailCutoffBound.Construction.radialTailWeight s ε R t| ≤ 1 / t := by
  rw [RadialTailCutoffBound.Construction.radialTailWeight, abs_mul, abs_of_nonneg (RadialTailCutoffBound.Construction.radialCutoff_nonneg R t),
    abs_of_nonneg (RealPower.Construction.realPowerWeight_nonneg s ε t ht)]
  calc
    _ ≤ 1 * t⁻¹ := mul_le_mul (RadialTailCutoffBound.Construction.radialCutoff_le_one R t)
      (RealPower.Construction.realPowerWeight_le_inverse s ε t hε ht) (RealPower.Construction.realPowerWeight_nonneg s ε t ht) (by norm_num)
    _ = _ := by rw [one_mul, one_div]

theorem radialTailWeightDerivative_abs_le (s ε R t C : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hε : 0 ≤ ε) (ht : 0 < t) (hC : 0 ≤ C)
    (hcut : |RadialTailCutoffBound.Construction.radialCutoffDerivative R t| ≤ 2 * C / t) :
    |RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t| ≤ (2 * C + 1) / t ^ 2 := by
  have hw : |RealPower.Construction.realPowerWeight s ε t| ≤ 1 / t := by
    rw [abs_of_nonneg (RealPower.Construction.realPowerWeight_nonneg s ε t ht), one_div]
    exact RealPower.Construction.realPowerWeight_le_inverse s ε t hε ht
  have hw' := PowerWeightBounds.Construction.realPowerWeightDerivative_abs_le s ε t hs hs1 hε ht
  rw [RadialTailCutoffBound.Construction.radialTailWeightDerivative]
  calc
    _ ≤ |RadialTailCutoffBound.Construction.radialCutoffDerivative R t * RealPower.Construction.realPowerWeight s ε t| +
        |RadialTailCutoffBound.Construction.radialCutoff R t * RealPower.Construction.realPowerWeightDerivative s ε t| := abs_add_le _ _
    _ = |RadialTailCutoffBound.Construction.radialCutoffDerivative R t| * |RealPower.Construction.realPowerWeight s ε t| +
        RadialTailCutoffBound.Construction.radialCutoff R t * |RealPower.Construction.realPowerWeightDerivative s ε t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (RadialTailCutoffBound.Construction.radialCutoff_nonneg R t)]
    _ ≤ (2 * C / t) * (1 / t) + 1 * (1 / t ^ 2) := by
      gcongr
      exact RadialTailCutoffBound.Construction.radialCutoff_le_one R t
    _ = _ := by field_simp

theorem radialAnnulusWeight_laplacian_bound : ∃ D : ℝ, 0 < D ∧
    ∀ s ε R T t : ℝ, 0 < s → s ≤ 1 → 0 ≤ ε → 0 < R → 0 < T → 0 < t →
      |t * RadialAnnulusWeight.Construction.radialAnnulusWeightSecondDerivative s ε R T t + RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative s ε R T t| ≤
        D / t ^ 2 := by
  obtain ⟨C, hC, hcut⟩ := RadialTailCutoffBound.Construction.radialCutoff_derivative_bounds
  obtain ⟨D, hD, htail⟩ := RadialTailCutoffBound.Construction.radialTailWeight_laplacian_bound
  refine ⟨D + 2 * (2 * C) * (2 * C + 1) + (4 * C + 2 * C) * 1, by positivity,
    fun s ε R T t hs hs1 hε hR hT ht => ?_⟩
  obtain ⟨hT1, hT2⟩ := hcut T hT t ht
  have hR1 := (hcut R hR t ht).1
  have hp := RadialTailCutoffBound.Construction.radial_laplacian_product_bound t
    (RadialTailCutoffBound.Construction.radialTailWeight s ε R t) (RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R t)
    (RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R t)
    (1 - RadialTailCutoffBound.Construction.radialCutoff T t) (-RadialTailCutoffBound.Construction.radialCutoffDerivative T t) (-RadialTailCutoffBound.Construction.radialCutoffSecondDerivative T t)
    1 (2 * C + 1) D (2 * C) (4 * C) ht (by positivity) (by positivity)
    (sub_nonneg.mpr (RadialTailCutoffBound.Construction.radialCutoff_le_one T t)) (by linarith [RadialTailCutoffBound.Construction.radialCutoff_nonneg T t])
    (radialTailWeight_abs_le s ε R t hε ht)
    (radialTailWeightDerivative_abs_le s ε R t C hs hs1 hε ht hC.le hR1)
    (htail s ε R t hs hs1 hε hR ht)
    (by simpa only [abs_neg] using hT1) (by simpa only [abs_neg] using hT2)
  convert hp using 1
  congr 1
  rw [RadialAnnulusWeight.Construction.radialAnnulusWeight_laplacian]
  ring

end

end OAI.RepresentationTheory.Weil.Local.RadialAnnulusBound.Construction
