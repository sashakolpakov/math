import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChartCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenChartDetection

/-! # Locally Product Supported Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass.BundleCycles

noncomputable section

/-! Canonical supported cycle classes commute with morphisms covered
by actual open product charts. The global equality is detected on
constructed charts through every regular support point. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (f : E ⟶ X) (charts : ∀ z : E.left, Open.ProductChart.BundleCycles.SchemeOpenProductChart f z)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left))

include charts hC in
omit [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem locallyProductSupport_codimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom := by
  obtain ⟨z, hz⟩ := C.isIrreducible.nonempty
  exact (charts z).inverseImage_codimension B C hC hz p hp

include charts in
theorem schemeSupportedCycleClass_locally_product (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass E C p hc := by
  let c (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver E C)) := charts (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion E C x))
  apply Scheme.OpenChartDetection.BundleCycles.schemeSupportedClass_eq_of_open_charts E C p hc (fun x => (c x).total)
    (fun x => (c x).totalMap) (fun x => (c x).point_mem (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion E C x) rfl)
  intro x
  have hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion E C x) ∈ (C : Set E.left) :=
    (Set.ext_iff.mp (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range E C) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion E C x)).mp
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion_subset E C (Set.mem_range_self x))
  exact (c x).cycleClass_square B C hC hz p hp hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass.BundleCycles
