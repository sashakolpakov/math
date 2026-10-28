import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.LatticeVolumes

/-! # Scale Measure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ScaleMeasure.CM

noncomputable section

/-! Actual change of finite Haar measure under rational dilation,
and its positive unitary normalization factor. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM

variable {I : Type*} [Fintype I]

def factor (q : ℚ) (hq : q ≠ 0) : NNReal := by
  let : ((Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q)).IsAddHaarMeasure :=
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleEquiv q hq).isAddHaarMeasure_map (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q⁻¹)
  exact Measure.addHaarScalarFactor ((Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q)) (Constructed.FiniteMeasure.CM.measure I)

theorem factor_pos (q : ℚ) (hq : q ≠ 0) : 0 < factor (I := I) q hq := by
  let : ((Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q)).IsAddHaarMeasure :=
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleEquiv q hq).isAddHaarMeasure_map (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q⁻¹)
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem map_measure (q : ℚ) (hq : q ≠ 0) :
    (Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q) = factor (I := I) q hq • Constructed.FiniteMeasure.CM.measure I := by
  let : ((Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale (ι := I) q)).IsAddHaarMeasure :=
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleEquiv q hq).isAddHaarMeasure_map (Constructed.FiniteMeasure.CM.measure I)
      (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q) (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale_continuous q⁻¹)
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem integral_scale (q : ℚ) (hq : q ≠ 0) (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    (∫ x, f (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x) ∂(Constructed.FiniteMeasure.CM.measure I)) =
      (factor (I := I) q hq : ℂ) * ∫ x, f x ∂(Constructed.FiniteMeasure.CM.measure I) := by
  have he := (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScaleHomeomorph (ι := I) q hq).isClosedEmbedding.integral_map
    (μ := Constructed.FiniteMeasure.CM.measure I) f
  change (∫ x, f x ∂((Constructed.FiniteMeasure.CM.measure I).map (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q))) =
    ∫ x, f (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteScale q x) ∂(Constructed.FiniteMeasure.CM.measure I) at he
  rw [← he]
  rw [map_measure q hq, integral_smul_nnreal_measure]
  rfl

def normalizingScalar (q : ℚ) (hq : q ≠ 0) : ℝ := (Real.sqrt (factor (I := I) q hq : ℝ))⁻¹

theorem normalizingScalar_ne_zero (q : ℚ) (hq : q ≠ 0) :
    normalizingScalar (I := I) q hq ≠ 0 := by
  apply inv_ne_zero
  exact (Real.sqrt_pos.mpr (by exact_mod_cast factor_pos (I := I) q hq)).ne'

theorem normalizingScalar_sq (q : ℚ) (hq : q ≠ 0) :
    normalizingScalar (I := I) q hq ^ 2 * (factor (I := I) q hq : ℝ) = 1 := by
  have hc : (factor (I := I) q hq : ℝ) ≠ 0 := by exact_mod_cast (factor_pos (I := I) q hq).ne'
  have hs : (Real.sqrt (factor (I := I) q hq : ℝ)) ^ 2 = (factor (I := I) q hq : ℝ) :=
    Real.sq_sqrt (factor (I := I) q hq).property
  unfold normalizingScalar
  rw [inv_pow, hs, inv_mul_cancel₀ hc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ScaleMeasure.CM
