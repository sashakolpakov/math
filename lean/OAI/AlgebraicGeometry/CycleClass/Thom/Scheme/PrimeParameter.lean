import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeAmbient
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction

/-! # Prime Parameter -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeParameter.Constructions.Class

noncomputable section

/-! On every smaller open subset of a regular prime-divisor normal
neighborhood, the actual canonical divisor class is the pullback of
the normalized origin class along its holomorphic submersion parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions
  PrimeAmbientNormalPair.Constructions PrimeAmbient.Constructions.Class Normal.ParameterRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] (z : {x : X.left // Order.coheight x = 1})
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)))
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hU : U ≤ (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).openNeighborhood)

abbrev primeParameter := Normal.ParameterRestriction.Constructions.normalParameter (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU

theorem primeParameter_zero_iff (y : U) : primeParameter X z x U hU y = 0 ↔
    y.val ∈ Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)) :=
  PrimeAmbientNormalPair.Constructions.primeAmbientPair_zero_iff X z x (Normal.ParameterRestriction.Constructions.normalParameterInclusion (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU y)

theorem primeParameter_analytic : ContMDiff
    𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
    (primeParameter X z x U hU) :=
  Normal.ParameterRestriction.Constructions.normalParameter_analytic (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU (PrimeAmbientNormalPair.Constructions.primeAmbientPair_analytic X z x)

theorem primeParameter_submersion (y : U) : Function.Surjective
    (mfderiv 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) 𝓘(ℂ, Fin 1 → ℂ)
      (primeParameter X z x U hU) y) :=
  Normal.ParameterRestriction.Constructions.normalParameter_submersion (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU
    (PrimeAmbientNormalPair.Constructions.primeAmbientPair_mdifferentiable X z x) (PrimeAmbientNormalPair.Constructions.primeAmbientPair_analytic X z x) y

theorem primeParameter_mapsTo : Set.MapsTo
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (primeParameter X z x U hU ⁻¹' {0}ᶜ) (Set.range (RegularSupport.Constructions.supportInclusion X (SchemeDivisor.Purity.Constructions.primeSupport X z)))ᶜ := by
  intro y hy hs
  exact hy ((primeParameter_zero_iff X z x U hU y).mpr hs)

theorem parameterInclusion_mapsTo : Set.MapsTo
    (Normal.ParameterRestriction.Constructions.normalParameterInclusion (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU)
    (primeParameter X z x U hU ⁻¹' {0}ᶜ) (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x).relativeComplement := by
  intro y hy hs
  exact hy ((Normal.ParameterRestriction.Constructions.normalParameter_zero_iff (PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x) U hU y).mpr hs)

variable [AlgebraicGeometry.IsNoetherian X.left]

theorem supportedDivisorClass_parameter :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
      (primeParameter_mapsTo X z x U hU) 2 (SchemeDivisor.Module.Constructions.supportedDivisorClass X z) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (primeParameter X z x U hU)
      (A := primeParameter X z x U hU ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) 2
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) := by
  let Q := PrimeAmbientNormalPair.Constructions.primeAmbientPair X z x
  let j := Normal.ParameterRestriction.Constructions.normalParameterInclusion Q U hU
  let k := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Q.neighborhood
  have hj := parameterInclusion_mapsTo X z x U hU
  have hk := PrimeAmbient.Constructions.Class.ambientPair_mapsTo X z x
  have he : j ≫ k = Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) := by
    ext y
    rfl
  have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j k hj hk 2
  have hm := ThomOpenRestriction.Constructions.pairMap_congr he (fun _ hy => hk (hj hy))
    (primeParameter_mapsTo X z x U hU) 2
  have hcomp := ConcreteCategory.congr_hom (hc.trans hm) (SchemeDivisor.Module.Constructions.supportedDivisorClass X z)
  have hn := PrimeAmbient.Constructions.Class.supportedDivisorClass_ambientNormalRestriction X z x
  have hq : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj 2 Q.rationalClassFin =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (primeParameter X z x U hU)
        (A := primeParameter X z x U hU ⁻¹' {0}ᶜ) (B := {0}ᶜ) (fun _ hy => hy) 2
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) := by
    rw [Q.rationalClassFin_eq_normalPullback]
    exact ConcreteCategory.congr_hom
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j Q.normalCoordinate hj Q.normalCoordinate_mapsTo 2)
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
  exact hcomp.symm.trans ((congrArg
    (fun b => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) j hj 2 b) hn).trans hq)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrimeParameter.Constructions.Class
