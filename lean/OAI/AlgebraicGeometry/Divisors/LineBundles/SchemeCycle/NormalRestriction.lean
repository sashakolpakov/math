import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality

/-! # Normal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction.BundleCycles

noncomputable section

/-! The supported cycle class has the normalized normal-pair class
on every actual holomorphic normal neighborhood of its regular locus. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "B" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance : MetrizableSpace G := MetrizableSpace.subtype _

theorem schemeSupportedCycleClass_regularPairPullback {U : TopCat.{0}} (g : U ⟶ TopCat.of G)
    (A : Set U) (hg : Set.MapsTo g A (Set.range j)ᶜ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (g ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
        ((CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)).comp hg)
        (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp (ModuleCat.of ℚ ℚ) g (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
      hg (CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)) (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)
  exact h.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_restrict X Z p hp))

omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeRegularSupportThomClass_normalPair (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) (Fin p → ℂ) j x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z × (Fin p → ℂ))) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ
      P.openNeighborhood (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp) = P.rationalClassFin :=
  CycleClass.Thom.Degree.Constructions.ThomClass.complexThomClassInDegree_restrict j (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z)
    p (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportCodimension X Z p hp) x P hP

theorem schemeSupportedCycleClass_normalPair (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) (Fin p → ℂ) j x)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z × (Fin p → ℂ))) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
        ((CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (Scheme.SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)).comp
          (show Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood) P.relativeComplement
            (Set.range j)ᶜ from fun _ hy => hy))
        (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) = P.rationalClassFin :=
  (schemeSupportedCycleClass_regularPairPullback X Z p hp
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of G) P.neighborhood) P.relativeComplement (fun _ hy => hy)).trans
      (schemeRegularSupportThomClass_normalPair X Z p hp x P hP)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction.BundleCycles
