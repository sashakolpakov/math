import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart

/-! # Product Chart Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChartCycle.BundleCycles

noncomputable section

/-! The supported cycle-class square on a constructed open product
chart, expressed in the literal inverse-image pair used for detection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem relativePullback_eq_of_source_eq {U T : TopCat.{0}} (f : U ⟶ T) (S : Set T)
    (A : Set U) (hA : A = f ⁻¹' S) (hf : Set.MapsTo f A S) (n : ℕ)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T S n)
    (hab : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n b) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (A := f ⁻¹' S) (B := S) (fun _ hy => hy) n a =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (A := f ⁻¹' S) (B := S) (fun _ hy => hy) n b := by
  subst A
  exact hab

namespace SchemeOpenProductChart

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    {f : E ⟶ X} {z : E.left} (c : ProductChart.BundleCycles.SchemeOpenProductChart f z)
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left)) (hz : z ∈ (C : Set E.left))

local notation "S" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion E C))ᶜ

include hz in
theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChart.BundleCycles.SchemeOpenProductChart.cycleClass_square (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map c.totalMap)
      (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.totalMap ⁻¹' S) (B := S) (fun _ hy => hy) (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
        (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map c.totalMap)
      (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.totalMap ⁻¹' S) (B := S) (fun _ hy => hy) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass E C p hc) := by
  let := c.totalSupport_nonempty C hz
  let := c.baseSupport_nonempty B C hC hz
  let A := SupportRestriction.BundleCycles.openRestrictedSupport c.baseMap.left B
  let D := SupportRestriction.BundleCycles.openRestrictedSupport c.totalMap.left C
  have hA := SupportRestriction.BundleCycles.openRestrictedSupport_coe c.baseMap.left B
  have hD := SupportRestriction.BundleCycles.openRestrictedSupport_coe c.totalMap.left C
  have ha := SupportOver.BundleCycles.openRestrictedSupportOver_codimension c.baseMap B p hp
  have hd := SupportOver.BundleCycles.openRestrictedSupportOver_codimension c.totalMap C p hc
  have hlocal := ProductCycleSquare.BundleCycles.schemeSupportedCycleClass_on_open_product f c.baseMap c.totalMap c.fiber
    c.fiberProjection c.baseProjection c.product c.square B C A D hC hA hD p hp hc ha hd
  have hsource : (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion c.total D))ᶜ =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map c.totalMap ⁻¹' S := by
    rw [SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_pointRange c.totalMap C D hD, Set.preimage_compl]
  exact relativePullback_eq_of_source_eq (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map c.totalMap) S
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion c.total D))ᶜ hsource
    (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo c.totalMap C D hD) (2 * p) _ _ hlocal

end SchemeOpenProductChart

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ProductChartCycle.BundleCycles
