import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.AmbientNormalRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction

/-! # Parameter Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.ParameterClass.BundleCycles

noncomputable section

/-! On a smaller neighborhood of any regular cycle point, its canonical supported class is the pullback of the normalized origin class along the actual holomorphic normal parameter, in arbitrary codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (Z : IrreducibleCloseds X.left) (q : ℕ)
  (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : U ≤ (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).openNeighborhood)

abbrev schemeSupportParameter := CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU

theorem schemeSupportParameter_zero_iff (y : U) : schemeSupportParameter X Z q hq x U hU y = 0 ↔
    y.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) :=
  Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_zero_iff X Z q hq x (CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameterInclusion (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU y)

theorem schemeSupportParameter_analytic : ContMDiff
    𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) 𝓘(ℂ, Fin q → ℂ) ω
    (schemeSupportParameter X Z q hq x U hU) :=
  CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter_analytic (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_analytic X Z q hq x)

theorem schemeSupportParameter_submersion (y : U) : Function.Surjective
    (mfderiv 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) 𝓘(ℂ, Fin q → ℂ)
      (schemeSupportParameter X Z q hq x U hU) y) :=
  CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter_submersion (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_mdifferentiable X Z q hq x) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_analytic X Z q hq x) y

theorem schemeSupportParameter_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (schemeSupportParameter X Z q hq x U hU ⁻¹' {0}ᶜ) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro y hy hs
  exact hy ((schemeSupportParameter_zero_iff X Z q hq x U hU y).mpr hs)

theorem schemeSupportParameterInclusion_mapsTo : Set.MapsTo
    (CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameterInclusion (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU)
    (schemeSupportParameter X Z q hq x U hU ⁻¹' {0}ᶜ) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).relativeComplement := by
  intro y hy hs
  exact hy ((CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter_zero_iff (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x) U hU y).mpr hs)

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem schemeSupportedCycleClass_parameter :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (schemeSupportParameter_mapsTo X Z q hq x U hU) (2 * q) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeSupportParameter X Z q hq x U hU)
      (A := schemeSupportParameter X Z q hq x U hU ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) (2 * q)
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q) := by
  let Q := Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x
  let j := CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameterInclusion Q U hU
  let k := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Q.neighborhood
  have hj := schemeSupportParameterInclusion_mapsTo X Z q hq x U hU
  have hk := AmbientNormalRestriction.BundleCycles.schemeSupportAmbientPair_mapsTo X Z q hq x
  have he : j ≫ k = CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
    ext y
    rfl
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j k hj hk (2 * q)
  have hm := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr he (fun _ hy => hk (hj hy))
    (schemeSupportParameter_mapsTo X Z q hq x U hU) (2 * q)
  have hcomp := ConcreteCategory.congr_hom (hc.trans hm) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq)
  have hn := AmbientNormalRestriction.BundleCycles.schemeSupportedCycleClass_ambientNormalRestriction X Z q hq x
  have hq : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj (2 * q) Q.rationalClassFin =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (schemeSupportParameter X Z q hq x U hU)
        (A := schemeSupportParameter X Z q hq x U hU ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) (2 * q)
        (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q) := by
    rw [Q.rationalClassFin_eq_normalPullback]
    exact ConcreteCategory.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j Q.normalCoordinate hj Q.normalCoordinate_mapsTo (2 * q))
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)
  exact hcomp.symm.trans ((congrArg
    (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj (2 * q) b) hn).trans hq)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.ParameterClass.BundleCycles
