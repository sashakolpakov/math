import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives

/-! # Filling Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.FillingCycle

noncomputable section

/-! Actual relative cycles and connecting boundaries from ambient fillings. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] (X : TopCat.{0}) (A : Set X) (n : ℕ)

theorem relativeFilling_is_cycle
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (n + 1))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of A)).X n)
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n z) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f (n + 1) B ∈
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains R X A) (n + 1) := by
  rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
  have h := ConcreteCategory.congr_hom ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).comm (n + 1) n) B
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains R X A).d (n + 1) n
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f (n + 1) B) =
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f n ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n B) at h
  rw [hB] at h
  exact h.trans (ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection R X A)) z)

def relativeFillingCycle
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (n + 1))
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of A)) n)
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n z.val) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains R X A) (n + 1) :=
  ⟨(CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection R X A).f (n + 1) B, relativeFilling_is_cycle R X A n B z.val hB⟩

theorem relativeFillingCycle_boundary
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).X (n + 1))
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of A)) n)
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).d (n + 1) n B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion R X A).f n z.val) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R X A).δ (n + 1) n rfl
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains R X A) (n + 1) (relativeFillingCycle R X A n B z hB)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (TopCat.of A)) n z :=
  AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives.homologyConnecting_eq_of_lift (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence R X A)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact R X A) n (relativeFillingCycle R X A n B z hB)
    B z rfl hB.symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.FillingCycle
