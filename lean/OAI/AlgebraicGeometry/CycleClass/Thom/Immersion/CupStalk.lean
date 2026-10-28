import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GoodShift
import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupShiftSections
import OAI.AlgebraicGeometry.CycleClass.Thom.EvenCupHomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso

/-! # Cup Stalk -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CupStalk.Constructions.Construction

noncomputable section

/-! The genuine normalized Thom cup is a stalk quasi-isomorphism along the regular support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

include ha

theorem regularThomCocycle_normalPair (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
      Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction (TopCat.of Z.regularAmbientSpace)
      (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) a P.openNeighborhood) =
        P.rationalClassFin := by
  rw [EvenCupShiftSections.Constructions.relativeEvenCocycleOpenRestriction_class, ha]
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
      P.openNeighborhood (2 * p) Z.regularThomClass = P.rationalClassFin
  rw [Z.regularThomClass_restrict_normalPair x P hP,
    P.rationalClassFin_eq_normalPullback]

theorem regularThomCupGoodShift_normalPair_quasiIso (x : Z.regularAnalyticSpace)
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
      Z.regularComplementInclusion x)
    (hP : P.ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    QuasiIso (EvenCupComplex.Constructions.relativeEvenCupGoodShiftMap (TopCat.of P.neighborhood) P.relativeComplement
      (EvenCupPresheaf.Constructions.relativeEvenCocycleOpenRestriction (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) a P.openNeighborhood)) :=
  EvenCupHomology.Constructions.normalPairRelativeEvenCupGoodShift_quasiIso P
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding _
    (regularThomCocycle_normalPair Z a ha x P hP)

theorem regularThomCupGoodShiftSheaf_stalk_quasiIso (x : Z.regularAnalyticSpace) :
    QuasiIso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap
      (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
        Z.regularThomComplementOpen a) (Z.regularComplementInclusion x)) := by
  rw [← EvenCupShiftSections.Constructions.relativeEvenCupGoodShiftPresheafMap_lift]
  apply HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.sheafComplexLift_stalk_quasiIso_of_locally
  intro U hxU
  let P := Z.regularFixedNormalPair x
  obtain ⟨r,hr,hle,hsub⟩ := P.exists_restrictRadius_subset
    (U : Set Z.regularAmbientSpace) (U.isOpen.mem_nhds hxU)
  let Q := P.restrictRadius r hr hle
  refine ⟨Q.openNeighborhood,Q.point_mem_neighborhood,hsub,?_⟩
  apply EvenCupShiftSections.Constructions.relativeEvenCupGoodShiftPresheafMap_open_quasiIso
    (he := fun n hn => SheafPurity.Constructions.Construction.regularThomSheaf_exactAt_except Z n (by omega))
  exact regularThomCupGoodShift_normalPair_quasiIso Z a ha x Q
    (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CupStalk.Constructions.Construction
