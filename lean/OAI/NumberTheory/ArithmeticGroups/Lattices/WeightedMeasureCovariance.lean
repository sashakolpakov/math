import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Weighted Measure Covariance -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.WeightedMeasureCovariance.Construction

noncomputable section

/-! A measure-preserving transformation that multiplies a density
by a constant produces the reciprocal scaling of the weighted measure. -/

open scoped ENNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem withDensity_map_covariance
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X)
    (hf : MeasurePreserving f μ μ) (w : X → ℝ≥0∞) (hw : Measurable w)
    (c : ℝ≥0∞) (hscale : ∀ x, w (f x) = c * w x) :
    c • (μ.withDensity w).map f = μ.withDensity w := by
  ext s hs
  rw [Measure.smul_apply, Measure.map_apply hf.measurable hs,
    withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul c hw]
  have he : (fun x => c * w x) = fun x => w (f x) := funext (fun x => (hscale x).symm)
  rw [he]
  exact hf.setLIntegral_comp_preimage hs hw

theorem measurePreserving_product_of_opposite_scalings
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → X) (g : Y → Y) (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (hμ : c • μ.map f = μ) (hν : ν.map g = c • ν) :
    MeasurePreserving (Prod.map f g) (μ.prod ν) (μ.prod ν) := by
  refine ⟨hf.prodMap hg, ?_⟩
  rw [← Measure.map_prod_map μ ν hf hg, hν, Measure.prod_smul_right,
    ← Measure.prod_smul_left, hμ]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.WeightedMeasureCovariance.Construction
