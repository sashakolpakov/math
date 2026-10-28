import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations

/-! # Reference Supported Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ReferenceSupportedComparison.Constructions

noncomputable section

/-!
# DegreeTwo: compare the actual global supported classes locally

Both sides are pullbacks of global relative classes on the original
scheme: the actual first-Chern lift and the actual supported cycle class
with its support enlarged to the reference complement.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.DivisorClass.Chern.LocalEquations.AlgebraicLineBundle

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorRegular.Constructions.DivisorRegularThom

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
  (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (U : V.carrier.Opens)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
    Z.regularComplementInclusion x)
  (hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)

theorem referencePair_mapsTo :
    Set.MapsTo (SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P) (DivisorRegular.Constructions.DivisorRegularThom.referenceComplement L Z U x P hPU)
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) :=
  fun _ hy => hy

/-- The local normal calculation is an equality between restrictions of
the two genuine global supported classes. -/
theorem rationalSectionChern_eq_supportedCycle_on_normalPair [Nonempty U]
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (i : V.carrier) (hi : U ≤ L.trivializingOpen i)
    (p : Γ(V.carrier, U)) (hp : p ≠ 0) (v : Γ(V.carrier, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : V.carrier.functionField) =
      V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
    (hmd : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))
    (hcoord : ∀ y : P.neighborhood, P.normalCoordinate y 0 =
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p (DivisorRegular.Constructions.DivisorRegularThom.neighborhoodInclusion Z U x P hPU y)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P)
        (referencePair_mapsTo L Z U x P hPU) 2 L.rationalSectionChernRelativeClass =
      m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P)
          (referencePair_mapsTo L Z U x P hPU) 2
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of V.analyticSpace)) hO 2
            Z.rationalSupportedCycleClass)) := by
  let Q := ModuleCat.of ℚ ℚ
  let A := DivisorRegular.Constructions.DivisorRegularThom.referenceComplement L Z U x P hPU
  let j := DivisorRegular.Constructions.DivisorRegularThom.neighborhoodInclusion Z U x P hPU
  let g := SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P
  have hj := DivisorRegular.Constructions.DivisorRegularThom.referenceComplement_mapsTo L Z U x P hPU
  have hg := referencePair_mapsTo L Z U x P hPU
  have hC : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q g hg 2 L.rationalSectionChernRelativeClass =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 (L.rationalSectionLocalSupportedClass i U hi) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U : Set V.analyticSpace))
      hj (A := A) (B := L.referenceLocus U)
      (C := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace))
      (fun _ hy => hy) 2
    have hv := (ConcreteCategory.congr_hom hc L.rationalSectionChernRelativeClass).symm
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q g hg 2 L.rationalSectionChernRelativeClass =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of V.analyticSpace)
          (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation L.rationalReferenceOpen : Set V.analyticSpace)
          (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) 2 L.rationalSectionChernRelativeClass) at hv
    rw [L.rationalSectionChernRelativeClass_algebraic i U hi] at hv
    exact hv
  obtain ⟨hA, hlocal⟩ := DivisorRegular.Constructions.DivisorRegularThom.rationalSectionLocalClass_eq_regularThom L Z U x P hPU
    i hi p hp v m hm he hmd hcoord
  have hS : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q g hg 2
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of V.analyticSpace)) hO 2
        Z.rationalSupportedCycleClass) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction Q (TopCat.of Z.regularAmbientSpace)
          (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood 2 Z.regularThomClass) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q g (𝟙 (TopCat.of V.analyticSpace)) hg hO 2
    have hv := ConcreteCategory.congr_hom hc Z.rationalSupportedCycleClass
    exact hv.trans (SupportedCycleNormalRestriction.Constructions.rationalSupportedCycleClass_normalRestriction Z x P A hA)
  exact hC.trans (hlocal.trans (congrArg (fun a => m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • a)) hS.symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ReferenceSupportedComparison.Constructions
