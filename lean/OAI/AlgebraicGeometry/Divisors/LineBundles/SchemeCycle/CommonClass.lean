import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.GysinLocal
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction

/-! # Common Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonClass.BundleCycles

noncomputable section

/-! The actual canonical cycle Gysin class and original ambient
supported cycle class agree on the constructed common normal charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Scheme.ProperSupport.Constructions CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso
  CycleClass.Thom.Closed.SupportAnalyticImage.Constructions CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions
  CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian Y.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction
  CycleClass.Thom.Normal.Product.Constructions.Class

local notation "P" => OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x
local notation "hP" => And.left (And.right (OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonPair.BundleCycles.schemeCycleCommonOuterPair_spec i Z p hp q hq x))
local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonImageImmersion i Z p hp q hq x

theorem schemeClosedImageClass_commonThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (CommonSupport.BundleCycles.schemeCycleCommonCycle_mapsTo i Z p hp q hq x) (2 * (p + q))
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq)) = (C).regularThomClass :=
  LocalThom.BundleCycles.schemeSupportedCycleClass_localThom Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (CommonPair.BundleCycles.schemeClosedImageRegularPoint i Z x)
    (P).openNeighborhood (CommonPair.BundleCycles.schemeCycleCommonOuterPair_spec i Z p hp q hq x).2.2 C (CommonSupport.BundleCycles.schemeCycleCommonCycle_range i Z p hp q hq x)

variable [AlgebraicGeometry.IsNoetherian X.left]
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeCycleGysinClass_commonThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (CommonSupport.BundleCycles.schemeCycleCommonGysin_mapsTo i Z p hp q hq x) (2 * (p + q)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha) =
    (C).regularThomClass := by
  have hs := CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass.supportEquality (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) C (CommonSupport.BundleCycles.schemeCycleCommonImage_range i Z p hp q hq x)
  have hr := CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) hs
    (show Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (P).openNeighborhood)
      (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) from fun _ hy => hy)
    (CommonSupport.BundleCycles.schemeCycleCommonGysin_mapsTo i Z p hp q hq x) (2 * (p + q)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha)
  have hl := GysinLocal.BundleCycles.schemeClosedCycleGysinClass_restriction i Z p hp q hq x P hP a ha
  have ht := CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass.localGysinIso_normalClass (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) P (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z)
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_supported i Z p hp) (GysinLocal.BundleCycles.schemeCycleGysinParameter i Z p hp q hq x P hP)
    (GysinLocal.BundleCycles.schemeCycleGysinParameter_zero i Z p hp q hq x P hP) C (CommonSupport.BundleCycles.schemeCycleCommonImage_range i Z p hp q hq x)
    (CommonPair.BundleCycles.schemeCycleCommonOuterPair_mdifferentiable i Z p hp q hq x) (CommonPair.BundleCycles.schemeCycleCommonOuterPair_analytic i Z p hp q hq x)
    (CommonPair.BundleCycles.schemeCycleCommonOuterPair_symm_analytic i Z p hp q hq x)
    (ParameterClass.BundleCycles.schemeSupportParameter_analytic X Z q hq x (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP)
    (fun y _ => ParameterClass.BundleCycles.schemeSupportParameter_submersion X Z q hq x
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding) hP y) a ha
  exact hr.symm.trans ((congrArg (fun b => eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (P).neighborhood) A (2 * (p + q))) hs) b) hl).trans ht)

theorem schemeCycleGysinClass_eq_imageClass_on_commonChart :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (CommonSupport.BundleCycles.schemeCycleCommonGysin_mapsTo i Z p hp q hq x) (2 * (p + q)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ((P).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (CommonSupport.BundleCycles.schemeCycleCommonCycle_mapsTo i Z p hp q hq x) (2 * (p + q))
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq)) :=
  (schemeCycleGysinClass_commonThom i Z p hp q hq x a ha).trans (schemeClosedImageClass_commonThom i Z p hp q hq x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonClass.BundleCycles
