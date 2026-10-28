import OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction

/-! # Rational Regular Normal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.RationalRegularNormal

noncomputable section

/-! The actual rational-function boundary on a regular divisor normal chart
is its algebraic exponent times the actual supported cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.RationalUnitEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalBoundary.Constructions.LocalMultiplicity
  RationalBoundary.Constructions.Restriction HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {g : V.carrier.functionField}
  (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g) (Z : Geometric.DimensionCycles.DimensionCycleSupport V 1)
  (U : V.carrier.Opens) (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ) Z.regularComplementInclusion x)
  (hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)

local notation "T" => TopCat.of V.analyticSpace
local notation "A" => (OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P) ⁻¹' (OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace)

/-- Enlarge the actual divisor support to the actual rational-function unit complement. -/
def cycleWithUnitComplement
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T) hO 2 Z.rationalSupportedCycleClass

theorem rationalGlobalBoundary_regularNormal [Nonempty U]
    (hO : (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) ⊆
      (Set.range Z.analyticInclusion)ᶜ)
    (p : Γ(V.carrier, U)) (hp : p ≠ 0) (v : Γ(V.carrier, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : g = V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
    (hmd : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))
    (hcoord : ∀ y : P.neighborhood, P.normalCoordinate y 0 =
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p (HodgeConjecture.DegreeTwo.DivisorRegular.Constructions.DivisorRegularThom.neighborhoodInclusion Z U x P hPU y)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P)
      («A» := A) (fun _ hy => hy) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
    m • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P)
      («A» := A) (fun _ hy => hy) 2 (cycleWithUnitComplement D Z hO) := by
  let Q := ModuleCat.of ℚ ℚ
  let j := HodgeConjecture.DegreeTwo.DivisorRegular.Constructions.DivisorRegularThom.neighborhoodInclusion Z U x P hPU
  let k := HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.regularPairAmbientMap Z x P
  let f := RationalBoundary.Constructions.LocalMultiplicity.lineMap (Y := TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)) (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p)
  have hj : Set.MapsTo j A (RationalUnitEvaluation.Constructions.referenceLocus V.presentation D U) := fun _ hy => hy
  have hk : Set.MapsTo k A (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation D.domain : Set V.analyticSpace) := fun _ hy => hy
  have hA : A ⊆ P.relativeComplement := by
    intro y hy
    exact (Z.mem_regularThomComplement_iff y.val).mpr (hO hy)
  let hp' := RationalUnitEvaluation.Constructions.referenceParameter_ne_zero V.presentation D U p v m he hp hm
  have hf : Set.MapsTo f (RationalUnitEvaluation.Constructions.referenceLocus V.presentation D U) PrincipalBoundary.Constructions.puncturedComplexLine :=
    RationalBoundary.Constructions.LocalMultiplicity.parameterMap_mapsTo V.presentation D U p hp'
  have hmap : j ≫ f = P.normalCoordinate := by
    ext y i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (hcoord y).symm
  have hC : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2 (RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary V.presentation D U) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j (RationalBoundary.Constructions.Restriction.localAmbientMap V.presentation U)
      hj (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo V.presentation D U) 2
    have hv := (ConcreteCategory.congr_hom hc (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D)).symm
    change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (RationalBoundary.Constructions.Restriction.localAmbientMap V.presentation U)
          (RationalBoundary.Constructions.Restriction.localAmbientMap_mapsTo V.presentation D U) 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D)) at hv
    rw [RationalBoundary.Constructions.Restriction.rationalGlobalBoundary_localRestriction] at hv
    exact hv
  have hparam : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q j hj 2
      (RationalBoundary.Constructions.LocalMultiplicity.parameterSupportedClass V.presentation D U p hp') =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        (P.normalCohomologyMap Q 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q j f hj hf 2
    simp only [hmap] at hc
    have hn := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q (𝟙 (TopCat.of P.neighborhood))
      P.normalCoordinate hA P.normalCoordinate_mapsTo 2
    simp only [Category.id_comp] at hn
    have hv := ConcreteCategory.congr_hom (hc.trans hn.symm) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)
    exact hv
  have hS : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (cycleWithUnitComplement D Z hO) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q (𝟙 (TopCat.of P.neighborhood)) hA 2
        (P.normalCohomologyMap Q 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) := by
    have hc := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp Q k (𝟙 T) hk hO 2
    have hv := ConcreteCategory.congr_hom hc Z.rationalSupportedCycleClass
    have hs := HodgeConjecture.DegreeTwo.SupportedCycleNormalRestriction.Constructions.rationalSupportedCycleClass_normalRestriction Z x P A hA
    rw [Z.regularThomClass_restrict_normalPair x P hmd] at hs
    exact hv.trans hs
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (RationalBoundary.Constructions.Restriction.rationalGlobalBoundary V.presentation D) =
    m • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap Q k hk 2 (cycleWithUnitComplement D Z hO)
  rw [hC, RationalBoundary.Constructions.LocalMultiplicity.rationalLocalBoundary_power V.presentation D U p hp v m hm he, map_zsmul, hparam, hS]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.RationalRegularNormal
