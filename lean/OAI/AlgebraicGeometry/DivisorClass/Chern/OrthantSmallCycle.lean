import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! # Orthant Small Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallCycle

noncomputable section

/-! The explicit oriented sphere has its actual small-chain connecting representative. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (n : ℕ)

local notation "CU" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantFirstChart n)
local notation "CV" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantSecondChart n)
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
  (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
local notation "jU" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion n)
local notation "jV" => OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion n)

def orthantEquatorCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OrthantBoundaryRepresentatives.orthantSphereOverlap n)) n :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OrthantSphereEquator.orderedEquatorOverlap n)) n (OrthantSphereCycle.orientedOrthantSphereCycle n)

theorem orthantEquatorCycle_val : (orthantEquatorCycle n).val = OrthantBoundaryRepresentatives.orthantEquatorChain n := by
  change (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OrthantSphereEquator.orderedEquatorOverlap n)).f n
    (OrthantSphereCycle.orientedOrthantSphereChain n) = _
  rw [OrthantSphereCycle.orientedOrthantSphereChain, OrthantBoundaryRepresentatives.orthantEquatorChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  rfl

def orthantMiddleChain : (S).X₂.X (n + 1) :=
  (biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n) +
    (biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)

theorem orthantMiddleChain_boundary :
    (S).f.f n (-(OrthantBoundaryRepresentatives.orthantEquatorChain n)) = (S).X₂.d (n + 1) n (orthantMiddleChain n) := by
  have hu : (jU).f n (-(OrthantBoundaryRepresentatives.orthantEquatorChain n)) = (CU).d (n + 1) n (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n) := by
    rw [map_neg, OrthantBoundaryRepresentatives.orthantFirstHemisphereChain_boundary]
  have hv : (jV).f n (-(OrthantBoundaryRepresentatives.orthantEquatorChain n)) = -((CV).d (n + 1) n (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)) := by
    rw [map_neg, OrthantBoundaryRepresentatives.orthantSecondHemisphereChain_boundary]
  have hf : (S).f = (jU) ≫ (biprod.inl : CU ⟶ CU ⊞ CV) -
      (jV) ≫ (biprod.inr : CV ⟶ CU ⊞ CV) := by
    simp only [CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_f, biprod.lift_eq, Preadditive.neg_comp, sub_eq_add_neg,
      OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion, OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion]
  have hl := ConcreteCategory.congr_hom ((biprod.inl : CU ⟶ CU ⊞ CV).comm (n + 1) n)
    (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n)
  have hr := ConcreteCategory.congr_hom ((biprod.inr : CV ⟶ CU ⊞ CV).comm (n + 1) n)
    (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)
  change (CU ⊞ CV).d (n + 1) n ((biprod.inl : CU ⟶ CU ⊞ CV).f (n + 1) _) =
    (biprod.inl : CU ⟶ CU ⊞ CV).f n ((CU).d (n + 1) n _) at hl
  change (CU ⊞ CV).d (n + 1) n ((biprod.inr : CV ⟶ CU ⊞ CV).f (n + 1) _) =
    (biprod.inr : CV ⟶ CU ⊞ CV).f n ((CV).d (n + 1) n _) at hr
  change (S).f.f n (-(OrthantBoundaryRepresentatives.orthantEquatorChain n)) = (CU ⊞ CV).d (n + 1) n (orthantMiddleChain n)
  rw [orthantMiddleChain, map_add, hl, hr, hf]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_sub, LinearMap.sub_apply, ConcreteCategory.comp_apply]
  have hL := congrArg (fun x : (CU).X n => (biprod.inl : CU ⟶ CU ⊞ CV).f n x) hu
  have hR := congrArg (fun x : (CV).X n => (biprod.inr : CV ⟶ CU ⊞ CV).f n x) hv
  refine (congrArg₂ (fun x y : (CU ⊞ CV).X n => x - y) hL hR).trans ?_
  rw [map_neg, sub_neg_eq_add]

def orientedOrthantSmallCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (S).X₃ (n + 1) :=
  ⟨(S).g.f (n + 1) (orthantMiddleChain n), by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((S).g.comm (n + 1) n) (orthantMiddleChain n)
    change (S).X₃.d (n + 1) n ((S).g.f (n + 1) (orthantMiddleChain n)) =
      (S).g.f n ((S).X₂.d (n + 1) n (orthantMiddleChain n)) at h
    rw [← orthantMiddleChain_boundary] at h
    exact h.trans (ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (S).zero) (-(OrthantBoundaryRepresentatives.orthantEquatorChain n)))⟩

def orientedOrthantSmallClass : CycleClass.Geometric.SmallSphereHomology.Cycles.spherePoleSmallHomology (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) (n + 1) :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (S).X₃ (n + 1) (orientedOrthantSmallCycle n)

theorem orientedOrthantSmallClass_boundary :
    CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))) n
      (orientedOrthantSmallClass n) =
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (OrthantBoundaryRepresentatives.orthantSphereOverlap n)) n (-(orthantEquatorCycle n)) := by
  apply AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift (S)
    (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) _ _) n
    (orientedOrthantSmallCycle n) (orthantMiddleChain n) (-(orthantEquatorCycle n)) rfl
  change (S).f.f n (-(orthantEquatorCycle n).val) = _
  rw [orthantEquatorCycle_val]
  exact orthantMiddleChain_boundary n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallCycle
