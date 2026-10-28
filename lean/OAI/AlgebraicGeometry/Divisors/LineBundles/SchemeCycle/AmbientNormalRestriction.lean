import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportAmbientNormalPair
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Ambient Normal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientNormalRestriction.BundleCycles

noncomputable section

/-! In actual ambient normal coordinates the full supported cycle class
is the canonical normal class, in arbitrary codimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

theorem schemeSupportAmbientPair_mapsTo :
    Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).neighborhood)
      (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).relativeComplement (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro y hy hs
  exact (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).normalCoordinate_mapsTo hy
    ((Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_zero_iff X Z p hp x y).mpr hs)

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem schemeSupportedCycleClass_ambientNormalRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).neighborhood)
        (schemeSupportAmbientPair_mapsTo X Z p hp x) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) =
      (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).rationalClassFin := by
  let P := (Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair x
  let G := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let k := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)
  let j := CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.liftedNormalInverse G P
  have hk : Set.MapsTo k P.relativeComplement (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ :=
    (CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ G
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)).comp
      (show Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood) P.relativeComplement
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z))ᶜ from fun _ hy => hy)
  have hj := CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.inverse_mapsTo G P
  have hv : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k hk (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) = P.rationalClassFin :=
    NormalRestriction.BundleCycles.schemeSupportedCycleClass_normalPair X Z p hp x P
      ((Scheme.SupportRegularImmersion.BundleCycles.schemeSupportRegularImmersion X Z p hp).regularFixedNormalPair_ambientChart_mdifferentiable x)
  have he : j ≫ k = CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).neighborhood := by
    ext y
    rfl
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j k hj hk (2 * p)
  have hm := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr he
    (fun _ hy => hk (hj hy)) (schemeSupportAmbientPair_mapsTo X Z p hp x) (2 * p)
  have hcomp := ConcreteCategory.congr_hom (hc.trans hm) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)
  exact hcomp.symm.trans ((congrArg
    (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj (2 * p) b) hv).trans
      (CycleClass.Thom.Open.NormalNeighborhoodInverse.Constructions.inverse_normalClass G P))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientNormalRestriction.BundleCycles
