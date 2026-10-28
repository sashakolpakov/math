import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentSection

/-! # Global Section Support Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionSupportRestriction.BundleCycles

noncomputable section

/-! Restricting an actual global section to an open chart preserves its literal zero support and the finite parent intersection support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation

variable {N Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral N.left] [Smooth N.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(N.left, ⊤))

omit [IsAffine Y.left] in
theorem globalSection_baseOpen_evaluation (x : U) :
    DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) (j.left.appTop s) = DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation x.val s :=
  (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map j (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU x) s).symm.trans
    (congrArg (fun y => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation y s) (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes j U hU x))

omit [IsAffine Y.left] in
theorem globalSection_baseImage_range :
    Set.range (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s)) =
      (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) ⁻¹' Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s) := by
  rw [CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  ext x
  exact (congrArg (fun t : ℂ => t = 0) (globalSection_baseOpen_evaluation j U hU s x)).to_iff

omit [IsAffine Y.left] in
theorem globalSection_baseImage_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (Set.range (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s)))ᶜ (Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage N s))ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (globalSection_baseImage_range j U hU s) x).mpr hy)

omit [IsAffine Y.left] in
theorem globalSection_baseEquation_square :
    CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU ≫ CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation Y (j.left.appTop s) =
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ≫ CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionEquation N s := by
  ext x i
  exact globalSection_baseOpen_evaluation j U hU s x

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]

omit [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
omit [IsAffine Y.left] in
theorem globalSection_finiteIntersection_range :
    Set.range (BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range (SectionSupport.BundleCycles.finiteBaseSectionImage j U hU (j.left.appTop s)) =
      (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) ⁻¹' RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s := by
  rw [BaseImageClass.BundleCycles.finiteBaseImage_range, globalSection_baseImage_range]
  rfl

omit [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
theorem finiteParentBaseImage_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))
    (Set.range (BaseImageClass.BundleCycles.finiteBaseImage k U))ᶜ
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (BaseImageClass.BundleCycles.finiteBaseImage_range k U) x).mpr hy)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GlobalSectionSupportRestriction.BundleCycles
