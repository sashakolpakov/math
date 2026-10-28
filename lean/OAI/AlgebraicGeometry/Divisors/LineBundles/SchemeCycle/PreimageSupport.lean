import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedOpenPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularTo

/-! # Preimage Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport.BundleCycles

noncomputable section

/-! The open and projection comparisons depend only on the actual
inverse-image support, so they apply to any equal reduced support description. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem schemeSupportPreimage_pointRange {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (B : IrreducibleCloseds Y.left) (C : IrreducibleCloseds X.left)
    (hC : (C : Set X.left) = f.left ⁻¹' (B : Set Y.left)) :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X C) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B) := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, hC]
  rfl

theorem schemeSupportPreimage_mapsTo {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (B : IrreducibleCloseds Y.left) (C : IrreducibleCloseds X.left)
    (hC : (C : Set X.left) = f.left ⁻¹' (B : Set Y.left)) :
    Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X C))ᶜ
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B))ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (schemeSupportPreimage_pointRange f B C hC) x).mpr hy)

theorem schemeSupportedCycleClass_open_of_support {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (i : X ⟶ Y) [IsOpenImmersion i.left] (B : IrreducibleCloseds Y.left)
    [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i.left B)]
    (C : IrreducibleCloseds X.left) (hC : (C : Set X.left) = i.left ⁻¹' (B : Set Y.left))
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeSupportPreimage_mapsTo i B C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X C p hc := by
  have he : C = Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B :=
    SetLike.coe_injective (hC.trans (Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe i.left B).symm)
  subst C
  exact Scheme.SupportedOpenPullback.BundleCycles.schemeSupportedCycleClass_openPullback i B p hp

theorem schemeSupportedCycleClass_projection_of_support
    (F X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral F.left] [Smooth F.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints F)] [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (E : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral E.left] [Smooth E.hom]
    [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
    (πF : E ⟶ F) (πX : E ⟶ X) (hprod : IsLimit (BinaryFan.mk πF πX))
    (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
    (hC : (C : Set E.left) = πX.left ⁻¹' (B : Set X.left))
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πX)
      (schemeSupportPreimage_mapsTo πX B C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp) =
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass E C p hc := by
  have he : C = Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport F X B E πF πX hprod :=
    SetLike.coe_injective (hC.trans (Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport_coe F X B E πF πX hprod).symm)
  subst C
  exact Projection.RegularTo.BundleCycles.schemeSupportedCycleClass_projection F X B E πF πX hprod p hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport.BundleCycles
