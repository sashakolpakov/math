import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorZero
import OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney

/-! # Relative Alexander Whitney -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeAlexanderWhitney.Constructions

noncomputable section

/-!
# DegreeTwo: the canonical Alexander–Whitney map respects product supports

After projecting both tensor factors to their actual relative quotients,
the canonical front/back map kills chains contained in either product
subspace. This uses the canonical diagonal formula and its naturality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable (k : Type) [Field k]

theorem productAlexanderWhitney_map {X Y Z : TopCat.{0}}
    (f : Z ⟶ TopCat.of (X × Y)) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ≫ AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X,Y) =
      AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.AlexanderWhitney.diagonal (TopCat.toSSet.obj Z) ≫
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (f ≫ TopCat.prodFst) ⊗ₘ
          (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map (f ≫ TopCat.prodSnd)) := by
  have hn := AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.AlexanderWhitney.diagonal_naturality
    (k := k) (TopCat.toSSet.map f)
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ≫
    AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.AlexanderWhitney.diagonal (TopCat.toSSet.obj (TopCat.of (X × Y))) =
    AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.AlexanderWhitney.diagonal (TopCat.toSSet.obj Z) ≫
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ⊗ₘ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f) at hn
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ≫
      AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.AlexanderWhitney.diagonal _ ≫
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map TopCat.prodFst ⊗ₘ
          (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map TopCat.prodSnd) = _
  rw [← Category.assoc, hn, Category.assoc, tensorHom_comp_tensorHom,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]

def relativeAlexanderWhitneyPre (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X × Y)) ⟶
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k Y B :=
  AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X,Y) ≫ (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B)

theorem relativeAlexanderWhitneyPre_left (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) ≫
      relativeAlexanderWhitneyPre k X Y A B = 0 := by
  rw [relativeAlexanderWhitneyPre, ← Category.assoc, productAlexanderWhitney_map,
    Category.assoc, tensorHom_comp_tensorHom]
  have hz := RelativeCrossSupport.Constructions.scalarChainMap_relativeProjection_zero k
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) ≫ TopCat.prodFst) A (by
      rintro _ ⟨x, rfl⟩
      exact x.property)
  rw [hz, TensorZero.Constructions.tensorChainHom_zero_left, comp_zero]

theorem relativeAlexanderWhitneyPre_right (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X × Y)) (Prod.snd ⁻¹' B) ≫
      relativeAlexanderWhitneyPre k X Y A B = 0 := by
  rw [relativeAlexanderWhitneyPre, ← Category.assoc, productAlexanderWhitney_map,
    Category.assoc, tensorHom_comp_tensorHom]
  have hz := RelativeCrossSupport.Constructions.scalarChainMap_relativeProjection_zero k
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (X × Y)) (Prod.snd ⁻¹' B) ≫ TopCat.prodSnd) B (by
      rintro _ ⟨x, rfl⟩
      exact x.property)
  rw [hz, TensorZero.Constructions.tensorChainHom_zero_right, comp_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeAlexanderWhitney.Constructions
