import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupShiftSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCupHomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso

/-! # Regular Thom Cup Stalk -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomCupStalk.Constructions

noncomputable section

/-! The genuine normalized Thom cup is a stalk quasi-isomorphism along the regular divisor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

include ha

theorem regularThomCocycle_normalPair (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
      Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) a P.openNeighborhood) =
        P.rationalClassFin := by
  rw [RelativeCupShiftSections.Constructions.relativeTwoCocycleOpenRestriction_class, ha]
  change CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      P.openNeighborhood (2*1) Z.regularThomClass = P.rationalClassFin
  rw [Z.regularThomClass_restrict_normalPair x P hP,
    P.rationalClassFin_eq_normalPullback]

theorem regularThomCupGoodShift_normalPair_quasiIso (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
      Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ))) :
    QuasiIso (RelativeCupHomotopy.Constructions.relativeTwoCupGoodShiftMap (TopCat.of P.neighborhood) P.relativeComplement
      (RelativeCupPresheaf.Constructions.relativeTwoCocycleOpenRestriction (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) a P.openNeighborhood)) :=
  RelativeCupHomology.Constructions.normalPairRelativeTwoCupGoodShift_quasiIso P
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding _
    (regularThomCocycle_normalPair Z a ha x P hP)

theorem regularThomCupGoodShiftSheaf_stalk_quasiIso (x : Z.regularAnalyticSpace) :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap
      (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
        Z.regularThomComplementOpen a) (Z.regularComplementInclusion x)) := by
  rw [← RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap_lift]
  apply LocalStalkQuasiIso.Constructions.sheafComplexLift_stalk_quasiIso_of_locally
  intro U hxU
  let P := Z.regularFixedNormalPair x
  obtain ⟨r,hr,hle,hsub⟩ := P.exists_restrictRadius_subset
    (U : Set Z.regularAmbientSpace) (U.isOpen.mem_nhds hxU)
  let Q := P.restrictRadius r hr hle
  refine ⟨Q.openNeighborhood,Q.point_mem_neighborhood,hsub,?_⟩
  apply RelativeCupShiftSections.Constructions.relativeTwoCupGoodShiftPresheafMap_open_quasiIso
    (he := fun n hn => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z n (by omega))
  exact regularThomCupGoodShift_normalPair_quasiIso Z a ha x Q
    (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomCupStalk.Constructions
