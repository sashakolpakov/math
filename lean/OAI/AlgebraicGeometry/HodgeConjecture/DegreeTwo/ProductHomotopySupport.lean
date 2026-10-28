import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeAlexanderWhitney

/-! # Product Homotopy Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductHomotopySupport.Constructions

noncomputable section

/-!
# DegreeTwo: the canonical product homotopy preserves relative tensor supports

Naturality of the constructed Eilenberg–Zilber homotopy proves that its
components descend through both actual factor quotients.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable (k : Type) [Field k]

def crossAlexanderWhitneyHomotopy (X Y : TopCat.{0}) :
    Homotopy (RelativeCrossSupport.Constructions.singularChainCross k X Y ≫ AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X,Y))
      (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X ⊗ AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) :=
  ((evaluation AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.SpacePair (ModuleCat.{0} k)).obj (X,Y)).mapHomotopy
    (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.canonicalHomotopyEquiv k).homotopyInvHomId

theorem crossAlexanderWhitneyHomotopy_naturality {X X' Y Y' : TopCat.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (a b : ℕ) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ⊗ₘ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map g).f a ≫
      (crossAlexanderWhitneyHomotopy k X' Y').hom a b =
    (crossAlexanderWhitneyHomotopy k X Y).hom a b ≫
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ⊗ₘ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map g).f b :=
  ((AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.canonicalHomotopyEquiv k).homotopyInvHomId.hom a b).naturality
    ((f,g) : (X,Y) ⟶ (X',Y'))

theorem crossAlexanderWhitneyHomotopy_left_zero
    (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (a b : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)).f a ≫
      (crossAlexanderWhitneyHomotopy k X Y).hom a b ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B).f b = 0 := by
  have hn := crossAlexanderWhitneyHomotopy_naturality k (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) (𝟙 Y) a b
  rw [CategoryTheory.Functor.map_id] at hn
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)).f a ≫
      (crossAlexanderWhitneyHomotopy k X Y).hom a b =
    (crossAlexanderWhitneyHomotopy k (TopCat.of A) Y).hom a b ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)).f b at hn
  have hz : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B) = 0 := by
    rw [tensorHom_comp_tensorHom, CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection,
      Category.id_comp, TensorZero.Constructions.tensorChainHom_zero_left]
  rw [← Category.assoc, hn, Category.assoc]
  have hz' : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)).f b ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B).f b = 0 :=
    HomologicalComplex.congr_hom hz b
  rw [hz', comp_zero]

theorem crossAlexanderWhitneyHomotopy_right_zero
    (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (a b : ℕ) :
    (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B).f a ≫
      (crossAlexanderWhitneyHomotopy k X Y).hom a b ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B).f b = 0 := by
  have hn := crossAlexanderWhitneyHomotopy_naturality k (𝟙 X) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) a b
  rw [CategoryTheory.Functor.map_id] at hn
  change (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B).f a ≫
      (crossAlexanderWhitneyHomotopy k X Y).hom a b =
    (crossAlexanderWhitneyHomotopy k X (TopCat.of B)).hom a b ≫
      (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B).f b at hn
  have hz : (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B) = 0 := by
    rw [tensorHom_comp_tensorHom, CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection,
      Category.id_comp, TensorZero.Constructions.tensorChainHom_zero_right]
  rw [← Category.assoc, hn, Category.assoc]
  have hz' : (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B).f b ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B).f b = 0 :=
    HomologicalComplex.congr_hom hz b
  rw [hz', comp_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ProductHomotopySupport.Constructions
