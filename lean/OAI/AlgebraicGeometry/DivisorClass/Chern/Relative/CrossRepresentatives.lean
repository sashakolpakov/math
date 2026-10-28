import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorArbitraryRepresentatives
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CrossBoundary

/-! # Cross Representatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossRepresentatives

noncomputable section

/-! The original relative homology cross product on actual tensor cycles
and its exact value on ambient quotient representatives. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions
open OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology
open scoped TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (p q : ℕ)

theorem relativeHomologyCrossClass_of_tensor_cycle
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) p)
    (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) q)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) (p + q))
    (hz : z.val = ιTensorObj (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B)
      p q (p + q) rfl (x.val ⊗ₜ[ℚ] y.val)) :
    HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass X Y A B p q (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ p x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ q y) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ X Y A B) (p + q) z) := by
  unfold HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass
  rw [TensorArbitraryRepresentatives.algebraicKunneth_of_tensor_cycle (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B)
    (p + q) ⟨(p, q), rfl⟩ x y z hz]
  exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ X Y A B) (p + q) z

theorem relativeSingularCross_quotient_representatives
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X q) :
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ X Y A B).f (p + q)
      (ιTensorObj (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) p q (p + q) rfl
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f p x ⊗ₜ[ℚ]
          (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f q y)) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B)).f (p + q)
        (Singular.CrossBoundary.singularCrossChain ℚ X Y p q (p + q) rfl x y) := by
  have ht := ConcreteCategory.congr_hom
    (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X)
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A)
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B) (p + q) ⟨(p, q), rfl⟩) (x ⊗ₜ[ℚ] y)
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f (p + q)
    (ιTensorObj (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y)
      p q (p + q) rfl (x ⊗ₜ[ℚ] y)) =
      ιTensorObj (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ Y B) p q (p + q) rfl
        (TensorProduct.map ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f p).hom
          ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f q).hom (x ⊗ₜ[ℚ] y)) at ht
  rw [TensorProduct.map_tmul] at ht
  rw [← ht]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f => f.f (p + q)) (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_projection ℚ X Y A B))
    (ιTensorObj (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y)
      p q (p + q) rfl (x ⊗ₜ[ℚ] y))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossRepresentatives
