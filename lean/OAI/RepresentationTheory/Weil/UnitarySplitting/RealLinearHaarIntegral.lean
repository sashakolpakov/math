import OAI.RepresentationTheory.Weil.UnitarySplitting.RealBilinearFourier
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Real Linear Haar Integral -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealLinearHaarIntegral.Construction

noncomputable section

/-! Real linear coordinate changes expose the determinant factor in Haar integrals. -/

open _root_.MeasureTheory

theorem realHaar_integral_comp_symm
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (D : V ≃L[ℝ] V) (f : V → ℝ) :
    (∫ v, f (D.symm v) ∂μ) = |LinearMap.det D.toLinearEquiv.toLinearMap| * ∫ v, f v ∂μ := by
  have hd : LinearMap.det D.symm.toLinearEquiv.toLinearMap ≠ 0 :=
    D.symm.toLinearEquiv.isUnit_det'.ne_zero
  have hds : LinearMap.det D.symm.toLinearEquiv.toLinearMap =
      (LinearMap.det D.toLinearEquiv.toLinearMap)⁻¹ := ContinuousLinearEquiv.det_coe_symm D
  calc
    _ = ∫ v, f v ∂μ.map D.symm := (D.symm.toHomeomorph.isClosedEmbedding.integral_map f).symm
    _ = _ := by
      change (∫ v, f v ∂μ.map D.symm.toLinearEquiv.toLinearMap) = _
      rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
        ENNReal.toReal_ofReal (abs_nonneg _), hds, inv_inv, smul_eq_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealLinearHaarIntegral.Construction
