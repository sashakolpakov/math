import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport

/-! # Cross Quotient Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CrossQuotientSupport.Constructions

noncomputable section

/-! Support factorization of the actual cross product for arbitrary target quotients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

variable (k : Type) [Field k]

theorem scalarChainMap_quotient_zero {X Y : TopCat.{0}}
    (f : X ⟶ Y) (A : Set Y) (hf : Set.range f ⊆ A)
    {E : ChainComplex (ModuleCat.{0} k) ℕ} (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y ⟶ E)
    (hq : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y A ≫ q = 0) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor k).map f ≫ q = 0 := by
  let g : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x => ⟨f x, hf ⟨x, rfl⟩⟩, f.hom.continuous.subtype_mk _⟩
  have hfg : g ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y A = f := rfl
  rw [← hfg, CategoryTheory.Functor.map_comp, Category.assoc]
  change _ ≫ (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y A ≫ q) = 0
  rw [hq, comp_zero]

theorem singularChainCross_left_quotient_zero (X Y : TopCat.{0}) (A : Set X)
    {E : ChainComplex (ModuleCat.{0} k) ℕ}
    (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X × Y)) ⟶ E)
    (hq : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X × Y)) (Prod.fst ⁻¹' A) ≫ q = 0) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) ≫
      RelativeCrossSupport.Constructions.singularChainCross k X Y ≫ q = 0 := by
  have hn := RelativeCrossSupport.Constructions.singularChainCross_naturality k (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) (𝟙 Y)
  rw [CategoryTheory.Functor.map_id] at hn
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X A ⊗ₘ 𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y)) ≫
    RelativeCrossSupport.Constructions.singularChainCross k X Y = _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hz := scalarChainMap_quotient_zero k
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A, 𝟙 Y) : (TopCat.of A,Y) ⟶ (X,Y)))
    (Prod.fst ⁻¹' A) (by rintro _ ⟨x,rfl⟩; exact x.1.property) q hq
  exact (congrArg (fun u => RelativeCrossSupport.Constructions.singularChainCross k (TopCat.of A) Y ≫ u) hz).trans comp_zero

theorem singularChainCross_right_quotient_zero (X Y : TopCat.{0}) (B : Set Y)
    {E : ChainComplex (ModuleCat.{0} k) ℕ}
    (q : AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X × Y)) ⟶ E)
    (hq : CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k (TopCat.of (X × Y)) (Prod.snd ⁻¹' B) ≫ q = 0) :
    (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B) ≫
      RelativeCrossSupport.Constructions.singularChainCross k X Y ≫ q = 0 := by
  have hn := RelativeCrossSupport.Constructions.singularChainCross_naturality k (𝟙 X) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B)
  rw [CategoryTheory.Functor.map_id] at hn
  change (𝟙 (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y B) ≫
    RelativeCrossSupport.Constructions.singularChainCross k X Y = _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hz := scalarChainMap_quotient_zero k
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X,CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y B) : (X,TopCat.of B) ⟶ (X,Y)))
    (Prod.snd ⁻¹' B) (by rintro _ ⟨x,rfl⟩; exact x.2.property) q hq
  exact (congrArg (fun u => RelativeCrossSupport.Constructions.singularChainCross k X (TopCat.of B) ≫ u) hz).trans comp_zero

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CrossQuotientSupport.Constructions
