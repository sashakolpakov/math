import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.IntersectionGysin

/-! # Supported Image Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageGenerator.BundleCycles

noncomputable section

/-! Supported Gysin carries each actual supported graded generator to its full closed-immersion image in the common intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions

theorem schemeClosedRelativeGenerator_of_support_eq (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (d p : ℕ)
    (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    (Z : IrreducibleCloseds Y.left)
    (hZ : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (he : irreducibleSetEquivPoints.symm x.val.val = Z)
    (hm : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) Fᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y Z))ᶜ) :
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator Y F d p hd x =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) hm (2 * p)
        (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y Z p hZ) := by
  subst Z
  rfl

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  (hv : IsOpen (Set.range v)ᶜ) (d r q : ℕ)
  (hr : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + r = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hd : d + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hr hd in
omit [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem closedSupportedImage_codimension : d + (r + q) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have hX := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
  have hY := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom
  omega

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr).regularComplementInclusion)ᶜ) (2 * r))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * r) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr).regularThomClass)

theorem closedSupportedImageGenerator_gysin
    (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr) a ha v hv).hom
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d q hd x) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d (r + q)
      (closedSupportedImage_codimension d r q hr hd) (SupportedImageCycle.BundleCycles.closedSupportedImagePoint i v d x) := by
  let Z := irreducibleSetEquivPoints.symm x.val.val
  let hq := (congrArg (fun n => n + q) x.val.property).trans hd
  have h := SchemeCycle.IntersectionGysin.BundleCycles.schemeCycleIntersectionGysin_imageClass i Z v (SupportedImageCycle.BundleCycles.closedSupportedImagePoint_subset i v d x)
    hv r hr q hq a ha
  have he := schemeClosedRelativeGenerator_of_support_eq Y
    (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d (r + q)
    (closedSupportedImage_codimension d r q hr hd) (SupportedImageCycle.BundleCycles.closedSupportedImagePoint i v d x)
    (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z r hr q hq)
    (Finite.GradedOverPushforward.BundleCycles.finiteOverDimensionPoint_support i d x.val)
    (SchemeCycle.IntersectionGysin.BundleCycles.schemeCycleIntersection_target_mapsTo i Z v (SupportedImageCycle.BundleCycles.closedSupportedImagePoint_subset i v d x))
  exact h.trans he.symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageGenerator.BundleCycles
