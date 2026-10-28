import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality

/-! # Absolute Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass.BundleCycles

noncomputable section

/-! Forgetting support gives the ordinary cohomology class of an
integral cycle on a smooth complex scheme, with its actual Thom restriction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (Z : IrreducibleCloseds X.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

local notation "T" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z
local notation "B" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z

def schemeAbsoluteCycleClass : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T B (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)

def schemeCycleClass : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (p + p) :=
  cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n : Type)) (two_mul p))
    (schemeAbsoluteCycleClass X Z p hp)

theorem schemeAbsoluteCycleClass_regularRestriction :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T)) (2 * p)
        (schemeAbsoluteCycleClass X Z p hp) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of G) (Set.range j)ᶜ (2 * p)
        (SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass X Z p hp) := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion T (G : Set T))
      (CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo T B G (Set.range j)ᶜ (SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X Z)) (2 * p))
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)
  exact h.symm.trans (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ)
    (TopCat.of G) (Set.range j)ᶜ (2 * p)) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_restrict X Z p hp))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass.BundleCycles
