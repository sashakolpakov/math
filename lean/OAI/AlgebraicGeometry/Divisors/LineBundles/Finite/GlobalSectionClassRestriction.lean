import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionSupportRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Global Section Class Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionClassRestriction.BundleCycles

noncomputable section

section

/-! The canonical global section and parent cycle classes restrict to the literal classes used in the constructed finite affine graph formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

def schemeSectionSupportedClass (N : Over Foundations.Scheme.ProjectiveSpace.complexBase) (s : Γ(N.left, ⊤)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
      (Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s))ᶜ 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation N s)
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo N s) 2 (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

variable {N Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral N.left] [Smooth N.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(N.left, ⊤))

omit [IsAffine Y.left] in
theorem globalSection_baseClass_pullback :
    CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU (j.left.appTop s) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (GlobalSectionSupportRestriction.BundleCycles.globalSection_baseImage_mapsTo j U hU s) 2 (schemeSectionSupportedClass N s) := by
  let hL := CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_mapsTo (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y (j.left.appTop s))
  let hR := GlobalSectionSupportRestriction.BundleCycles.globalSection_baseImage_mapsTo j U hU s
  let hj := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  have hl := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU)
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y (j.left.appTop s)) hL (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y (j.left.appTop s)) 2
  have hr := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) hj
    (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation N s) hR (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo N s) 2
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (GlobalSectionSupportRestriction.BundleCycles.globalSection_baseEquation_square j U hU s)
    ((CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo Y (j.left.appTop s)).comp hL) ((CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation_mapsTo N s).comp hR) 2
  exact ConcreteCategory.congr_hom (hl.trans (he.trans hr.symm)) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

omit [AlgebraicGeometry.IsNoetherian S.left] in
theorem finiteBaseImageClass_eq_pullback :
    BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (GlobalSectionSupportRestriction.BundleCycles.finiteParentBaseImage_mapsTo U k) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (ParentGraphProjection.BundleCycles.finiteWholeImage_codimension k p hp)) := by
  exact CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (congrArg Set.compl (BaseImageClass.BundleCycles.finiteBaseImage_range k U).symm)
    (show Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (BaseImageClass.BundleCycles.finiteParentBaseSupport k U)ᶜ
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))ᶜ from fun _ hx => hx)
    (GlobalSectionSupportRestriction.BundleCycles.finiteParentBaseImage_mapsTo U k) (2 * p)
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (ParentGraphProjection.BundleCycles.finiteWholeImage_codimension k p hp))

end

/-! The global supported finite-image section cup restricts to the literal local cup in the constructed affine formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

omit [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
theorem finiteParentImage_openComplement :
    IsOpen (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))ᶜ :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)))).isClosed_range.isOpen_compl

def finiteGlobalSectionCup : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ (2 * (p + 1)) :=
  CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s)
    (finiteParentImage_openComplement k) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement N s) p 1
    ((k.left.residueDegree (genericPoint S.left) : ℚ) •
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (ParentGraphProjection.BundleCycles.finiteWholeImage_codimension k p hp))
    (schemeSectionSupportedClass N s)

variable {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (j : Y ⟶ N) [IsOpenImmersion j.left] (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

omit [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] [IsAffine Y.left] in
theorem finiteGlobalSectionCup_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (Set.range (BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s)))ᶜ
    (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ :=
  CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s)
    (BaseImageClass.BundleCycles.finiteBaseImage k U) (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s))
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (GlobalSectionSupportRestriction.BundleCycles.finiteParentBaseImage_mapsTo U k) (GlobalSectionSupportRestriction.BundleCycles.globalSection_baseImage_mapsTo j U hU s)

omit [AlgebraicGeometry.IsNoetherian S.left] [IsAffine Y.left] in
theorem finiteGlobalSectionCup_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
      (finiteGlobalSectionCup_mapsTo k s j U hU) (2 * (p + 1)) (finiteGlobalSectionCup k s p hp) =
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImageClass.BundleCycles.finiteBaseImage k U) (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s))
      (BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y (j.left.appTop s))
        (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y (j.left.appTop s))) p 1
      ((k.left.residueDegree (genericPoint S.left) : ℚ) • BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U)
      (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU (j.left.appTop s)) := by
  have h := CycleClass.Thom.ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s)
    (BaseImageClass.BundleCycles.finiteBaseImage k U) (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s))
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (GlobalSectionSupportRestriction.BundleCycles.finiteParentBaseImage_mapsTo U k) (GlobalSectionSupportRestriction.BundleCycles.globalSection_baseImage_mapsTo j U hU s)
    (finiteParentImage_openComplement k) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement N s)
    (BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y (j.left.appTop s))
      (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y (j.left.appTop s))) p 1
    ((k.left.residueDegree (genericPoint S.left) : ℚ) •
      Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (ParentGraphProjection.BundleCycles.finiteWholeImage_codimension k p hp))
    (schemeSectionSupportedClass N s)
  rw [map_smul, ← finiteBaseImageClass_eq_pullback U k p hp,
    ← globalSection_baseClass_pullback j U hU s] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionClassRestriction.BundleCycles
