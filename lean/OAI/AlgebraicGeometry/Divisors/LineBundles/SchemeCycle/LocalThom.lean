import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.ParameterClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Equation
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup

/-! # Local Thom -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.LocalThom.BundleCycles

noncomputable section

/-! The original supported cycle class restricts to the genuine Thom
class of any actual closed immersion with the same local image inside
one of its canonical ambient normal charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction.Constructions
  CycleClass.Thom.Equation.Constructions.ThomClass CycleClass.Thom.ExteriorImageCup.Constructions.Restriction
  CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold CycleClass.Thom.Scheme.ClosedImmersion.Constructions
  CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian X.left]
  (Z : IrreducibleCloseds X.left) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : U ≤ (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x).openNeighborhood)
  (C : CycleClass.Thom.Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeManifold X) U) p)
  (hC : Set.range C.regularComplementInclusion = Subtype.val ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))

include hC in
omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleLocalEquation (y : U) : y ∈ Set.range C.regularComplementInclusion ↔ ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU y = 0 :=
  (Set.ext_iff.mp hC y).trans (ParameterClass.BundleCycles.schemeSupportParameter_zero_iff X Z p hp x U hU y).symm

include hC in
omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleLocalMapsTo : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Set.range C.regularComplementInclusion)ᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro y hy hd
  exact hy ((Set.ext_iff.mp hC y).mpr hd)

include hC in
omit [AlgebraicGeometry.IsNoetherian X.left] in
theorem schemeCycleParameterComplement : ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU ⁻¹' {0}ᶜ = (Set.range C.regularComplementInclusion)ᶜ := by
  ext y
  exact not_congr (schemeCycleLocalEquation X Z p hp x U hU C hC y).symm

include hU in
theorem schemeSupportedCycleClass_localThom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (schemeCycleLocalMapsTo X Z p U C hC) (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp) = C.regularThomClass := by
  have hpar := ParameterClass.BundleCycles.schemeSupportedCycleClass_parameter X Z p hp x U hU
  have hi := CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (schemeCycleParameterComplement X Z p hp x U hU C hC) (ParameterClass.BundleCycles.schemeSupportParameter_mapsTo X Z p hp x U hU) (schemeCycleLocalMapsTo X Z p U C hC)
    (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z p hp)
  have hf := CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast (ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU) (schemeCycleParameterComplement X Z p hp x U hU C hC)
    (show Set.MapsTo (ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU) (ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU ⁻¹' {0}ᶜ) {0}ᶜ from fun _ hy => hy)
    (CycleClass.Thom.Equation.Constructions.ThomClass.equation_mapsTo C (ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU) (schemeCycleLocalEquation X Z p hp x U hU C hC)) (2 * p)
    (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  have ht := CycleClass.Thom.Equation.Constructions.ThomClass.equation_pullback_eq_Thom C (ParameterClass.BundleCycles.schemeSupportParameter X Z p hp x U hU) (schemeCycleLocalEquation X Z p hp x U hU C hC)
    (CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter_analytic (G := (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x) U hU (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_analytic X Z p hp x))
    (fun y => CycleClass.Thom.Normal.ParameterRestriction.Constructions.normalParameter_submersion (G := (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z p hp x) U hU
      (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_mdifferentiable X Z p hp x) (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair_analytic X Z p hp x) (C.regularComplementInclusion y))
  exact hi.symm.trans ((congrArg (fun b => eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) A (2 * p))
    (schemeCycleParameterComplement X Z p hp x U hU C hC)) b) hpar).trans (hf.trans ht))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.LocalThom.BundleCycles
