import OAI.AlgebraicGeometry.DivisorClass.Chern.PrimitiveNormalWinding
import OAI.AlgebraicGeometry.CycleClass.Geometric.TraceNormalization

/-! # Winding Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.WindingNormalization

noncomputable section

/-!
# ChernClass: compare the fixed geometric normalization with positive monodromy

The actual integral filling of the positive exponential loop is a primitive
generator. Its normalized coordinate and the original geometric coordinate
differ by precisely the winding coefficient already present in the Chern
comparison. The existing classes and normalizations remain unchanged.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.TraceNormalization.Duality
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The integral coordinate of the genuine positive loop filling is the
same primitive sign as the positive winding cocycle's geometric coordinate. -/
theorem normalPositiveLoopCoefficient_cast :
    (PrimitiveNormalWinding.normalPositiveLoopCoefficient : ℚ) = NormalWinding.normalWindingCoefficient := by
  have h := PrimitiveNormalWinding.normalWindingCoefficient_integral_inverse
  rcases PrimitiveNormalWinding.normalWindingCoefficient_eq_one_or_neg_one with hp | hn
  · rw [hp] at h ⊢
    simpa only [one_mul] using h
  · rw [hn] at h ⊢
    linarith

theorem normalPositiveLoopCoefficient_mul_self :
    PrimitiveNormalWinding.normalPositiveLoopCoefficient * PrimitiveNormalWinding.normalPositiveLoopCoefficient = 1 := by
  have h := PrimitiveNormalWinding.normalWindingCoefficient_integral_inverse
  rw [← normalPositiveLoopCoefficient_cast] at h
  exact_mod_cast h

/-- The primitive integral unit supplied by the actual positive loop. -/
def positiveLoopUnit : ℤˣ where
  val := PrimitiveNormalWinding.normalPositiveLoopCoefficient
  inv := PrimitiveNormalWinding.normalPositiveLoopCoefficient
  val_inv := normalPositiveLoopCoefficient_mul_self
  inv_val := normalPositiveLoopCoefficient_mul_self

/-- A coordinate on the same actual local integral homology group that
sends the positive exponential loop filling to one. -/
def positiveWindingModelNormalization : CycleClass.Geometric.FundamentalNormalization.Cycles.ComplexModelNormalization 1 :=
  (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv 1).trans (LinearEquiv.smulOfUnit (M := ℤ) positiveLoopUnit)

theorem positiveWindingModelNormalization_positiveLoop :
    positiveWindingModelNormalization PrimitiveNormalWinding.normalPositiveLoopRelativeClass = 1 := by
  change PrimitiveNormalWinding.normalPositiveLoopCoefficient * PrimitiveNormalWinding.normalPositiveLoopCoefficient = 1
  exact normalPositiveLoopCoefficient_mul_self

/-- Its integral generator is exactly the original positive loop filling. -/
theorem positiveWindingModelNormalization_generator :
    positiveWindingModelNormalization.symm 1 = PrimitiveNormalWinding.normalPositiveLoopRelativeClass := by
  apply positiveWindingModelNormalization.injective
  rw [LinearEquiv.apply_symm_apply, positiveWindingModelNormalization_positiveLoop]

/-- The original geometric orientation coordinate differs by the
already measured positive-winding coefficient. -/
theorem positiveWindingModelNormalization_sign :
    (CycleClass.Geometric.FundamentalNormalization.Cycles.complexModelNormalizationSign 1 positiveWindingModelNormalization : ℚ) =
      NormalWinding.normalWindingCoefficient := by
  change ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv 1)
    (positiveWindingModelNormalization.symm 1) : ℚ) = _
  rw [positiveWindingModelNormalization_generator]
  exact normalPositiveLoopCoefficient_cast

/-- Exact agreement of the fixed geometric generator with the positive
loop is equivalent to fixing the remaining coefficient to positive one. -/
theorem normalWindingCoefficient_eq_one_iff_positive_generator :
    NormalWinding.normalWindingCoefficient = 1 ↔
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1 = PrimitiveNormalWinding.normalPositiveLoopRelativeClass := by
  constructor
  · intro h
    apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).toLinearEquiv.injective
    change (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1) =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom PrimitiveNormalWinding.normalPositiveLoopRelativeClass
    rw [Iso.inv_hom_id_apply]
    change 1 = PrimitiveNormalWinding.normalPositiveLoopCoefficient
    exact_mod_cast (normalPositiveLoopCoefficient_cast.trans h).symm
  · intro h
    have hc := congrArg (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom h
    rw [Iso.inv_hom_id_apply] at hc
    change 1 = PrimitiveNormalWinding.normalPositiveLoopCoefficient at hc
    rw [← normalPositiveLoopCoefficient_cast, ← hc]
    rfl

/-- Repeating the actual compact trace construction with the positive
loop generator changes the original curve trace by exactly this sign. -/
theorem positiveWindingTrace_eq_coefficient_smul
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin 1 → ℂ) M] [IsManifold 𝓘(ℂ, Fin 1 → ℂ) 1 M] :
    CycleClass.Geometric.TraceNormalization.Duality.complexManifoldTraceWithNormalization 1 positiveWindingModelNormalization (M := M) =
      NormalWinding.normalWindingCoefficient • AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := M) := by
  rw [CycleClass.Geometric.TraceNormalization.Duality.complexManifoldTraceWithNormalization_eq_sign_smul,
    positiveWindingModelNormalization_sign]

/-- Cap of the actual winding residue with the fixed integral normal
generator has augmentation equal to the measured geometric sign. -/
theorem normalWindingCap_canonicalGenerator :
    AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation NormalWinding.windingNormalLine
      (AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 0
        NormalWinding.normalSupportedWindingClass ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1)) =
      NormalWinding.normalWindingCoefficient := by
  rw [AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation_relativeCapHomology,
    NormalWinding.normalSupportedWindingClass_eq_coefficient_smul, map_smul]
  change NormalWinding.normalWindingCoefficient * AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation
    NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
      ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).inv 1) = _
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.complexNormalRationalDualClass_integralEvaluation, mul_one]

/-- The same actual cap construction evaluates to positive one on
the integral filling of the original positive exponential loop. -/
theorem normalWindingCap_positiveGenerator :
    AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation NormalWinding.windingNormalLine
      (AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 0
        NormalWinding.normalSupportedWindingClass PrimitiveNormalWinding.normalPositiveLoopRelativeClass) = 1 := by
  rw [AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation_relativeCapHomology]
  exact PrimitiveNormalWinding.normalPositiveLoopRelativeClass_winding

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.WindingNormalization
