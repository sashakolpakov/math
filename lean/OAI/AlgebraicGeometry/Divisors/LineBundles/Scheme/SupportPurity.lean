import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport

/-! # Support Purity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportPurity.BundleCycles

noncomputable section

/-! A support of codimension p has singular boundary of codimension
at least p + 1. Actual supported cohomology in degree 2p therefore
extends uniquely from its regular locus on a smooth complex scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (Z : IrreducibleCloseds X.left) (p : ℕ)

def schemeSupportSingularBoundary : Closeds X.left :=
  ⟨CycleClass.Geometric.StratumDimension.supportSingularBoundary Z X.hom, CycleClass.Geometric.StratumDimension.isClosed_supportSingularBoundary Z X.hom⟩

theorem schemeSupportSingularBoundary_dimension
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (W : IrreducibleCloseds X.left) (hW : (W : Set X.left) ⊆ schemeSupportSingularBoundary X Z) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + (p + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  have hlt := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W Z X.hom
    (CycleClass.Geometric.StratumDimension.lt_of_subset_supportSingularBoundary W Z X.hom hW)
  omega

omit [IsIntegral X.left] in
theorem schemeSupportComplement_subset_regularAmbient :
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z := by
  intro y hy hboundary
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq] at hboundary
  exact hy hboundary.1

variable [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]

theorem schemeSupportRegularRestriction_isIso
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) (2 * p)) := by
  have h0 := CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedSupport_cohomology_isZero
    X (schemeSupportSingularBoundary X Z) (p + 1)
    (schemeSupportSingularBoundary_dimension X Z p hp) (2 * p) (by omega)
  have h1 := CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedSupport_cohomology_isZero
    X (schemeSupportSingularBoundary X Z) (p + 1)
    (schemeSupportSingularBoundary_dimension X Z p hp) (2 * p + 1) (by omega)
  exact CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
    (schemeSupportComplement_subset_regularAmbient X Z) (2 * p) h0 h1

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportPurity.BundleCycles
