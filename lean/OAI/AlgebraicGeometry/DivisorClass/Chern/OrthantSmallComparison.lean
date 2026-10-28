import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives
import OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion

/-! # Orthant Small Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallComparison

noncomputable section

/-! The actual small-chain representative maps to the original orthant sphere. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orientedOrthantSmallCycle_inclusion (n : ℕ) :
    (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))).f (n + 1) (OrthantSmallCycle.orientedOrthantSmallCycle n).val = OrthantSphereCycle.orientedOrthantSphereChain (n + 1) := by
  let S := CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
  let j := CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
  let CU := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OrthantBoundaryRepresentatives.orthantFirstChart n)
  let CV := CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OrthantBoundaryRepresentatives.orthantSecondChart n)
  have hl : (biprod.inl : CU ⟶ CU ⊞ CV) ≫ S.g ≫ j =
      CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))) := by
    rw [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inl_desc_assoc]
    exact CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left _ _ _
  have hr : (biprod.inr : CV ⟶ CU ⊞ CV) ≫ S.g ≫ j =
      CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))) := by
    rw [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inr_desc_assoc]
    exact CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right _ _ _
  have hL := ConcreteCategory.congr_hom (congrArg (fun f => f.f (n + 1)) hl) (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n)
  have hR := ConcreteCategory.congr_hom (congrArg (fun f => f.f (n + 1)) hr) (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)
  change j.f (n + 1) (S.g.f (n + 1) ((biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) _ +
    (biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) _)) = _
  rw [map_add, map_add]
  change j.f (n + 1) (S.g.f (n + 1) ((biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) _)) = _ at hL
  change j.f (n + 1) (S.g.f (n + 1) ((biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) _)) = _ at hR
  rw [hL, hR, OrthantBoundaryRepresentatives.orthantFirstHemisphereChain_ambient, OrthantBoundaryRepresentatives.orthantSecondHemisphereChain_ambient]
  exact (OrthantBoundaryRepresentatives.orientedOrthantSphereChain_split n).symm

theorem orientedOrthantSmallClass_comparison (n : ℕ) :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (n + 1)).hom
      (OrthantSmallCycle.orientedOrthantSmallClass n) = OrthantSphereCycle.orientedOrthantSphereClass (n + 1) := by
  let j := CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
  refine (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality j (n + 1) (OrthantSmallCycle.orientedOrthantSmallCycle n)).trans ?_
  apply congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))) (n + 1))
  exact Subtype.ext (orientedOrthantSmallCycle_inclusion n)

theorem orientedOrthantSmallClass_lowerSphere (n : ℕ) :
    CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (n + 1)).toFun) n
      (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
        (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) n
        (OrthantSmallCycle.orientedOrthantSmallClass n)) = -(OrthantSphereCycle.orientedOrthantSphereClass n) := by
  rw [OrthantSmallCycle.orientedOrthantSmallClass_boundary, map_neg, map_neg]
  congr 1
  have he : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OrthantBoundaryRepresentatives.orthantSphereOverlap n)) n (OrthantSmallCycle.orthantEquatorCycle n) =
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (OrthantSphereEquator.orderedEquatorOverlap n) n (OrthantSphereCycle.orientedOrthantSphereClass n) :=
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OrthantSphereEquator.orderedEquatorOverlap n)) n
      (OrthantSphereCycle.orientedOrthantSphereCycle n)).symm
  rw [he]
  have hm : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (OrthantSphereEquator.orderedEquatorOverlap n) n ≫
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (n + 1)).toFun) n =
      𝟙 (CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) n) := by
    simp only [CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, OrthantSphereEquator.orderedEquatorOverlap_retraction]
    rw [CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map_id, HomologicalComplex.homologyMap_id]
  exact ConcreteCategory.congr_hom hm (OrthantSphereCycle.orientedOrthantSphereClass n)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallComparison
