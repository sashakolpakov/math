import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport

/-! # Associativity Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport

noncomputable section

/-! The associativity homotopy preserves all three actual factor supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity.Constructions

namespace Constructions

variable (k : Type) [Field k]

theorem associativity_map_into_subspace_zero {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y)
    (U : Set (TripleModels.Constructions.tripleSpace.obj Y)) (hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ U) (a b : ℕ) :
    (TripleCross.Constructions.tensorTripleMap k f).f a ≫ (Tensor.NaturalAssociativity.Constructions.associativity k Y).hom a b ≫
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj Y) U).f b = 0 := by
  have hz := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.scalarChainMap_relativeProjection_zero k (TripleModels.Constructions.tripleSpace.map f) U hf
  change (TripleModels.Constructions.tripleChainFunctor k).map f ≫
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj Y) U = 0 at hz
  have hzb := HomologicalComplex.congr_hom hz b
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hzb
  rw [← Category.assoc, Tensor.NaturalAssociativity.Constructions.associativity_natural, Category.assoc, hzb, comp_zero]

def tripleSupportComplement (X : TripleModels.Constructions.SpaceTriple)
    (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2) : Set (TripleModels.Constructions.tripleSpace.obj X) :=
  (fun x => x.1.1) ⁻¹' A ∪ (fun x => x.1.2) ⁻¹' B ∪ (fun x => x.2) ⁻¹' C

theorem associativity_first_zero (X : TripleModels.Constructions.SpaceTriple)
    (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2) (a b : ℕ) :
    ((Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.1 A ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.1.2)) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)).f a ≫ (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
          (tripleSupportComplement X A B C)).f b = 0 := by
  let f : ((TopCat.of A, X.1.2), X.2) ⟶ X :=
    ((Geometric.LocalHomology.Cycles.subspaceInclusion X.1.1 A, 𝟙 X.1.2), 𝟙 X.2)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inl (Or.inl x.1.1.property)
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id] using
    associativity_map_into_subspace_zero k f (tripleSupportComplement X A B C) hf a b

theorem associativity_second_zero (X : TripleModels.Constructions.SpaceTriple)
    (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2) (a b : ℕ) :
    ((𝟙 (TripleCross.Constructions.chains k X.1.1) ⊗ₘ Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.2 B) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)).f a ≫ (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
          (tripleSupportComplement X A B C)).f b = 0 := by
  let f : ((X.1.1, TopCat.of B), X.2) ⟶ X :=
    ((𝟙 X.1.1, Geometric.LocalHomology.Cycles.subspaceInclusion X.1.2 B), 𝟙 X.2)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inl (Or.inr x.1.2.property)
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id] using
    associativity_map_into_subspace_zero k f (tripleSupportComplement X A B C) hf a b

theorem associativity_third_zero (X : TripleModels.Constructions.SpaceTriple)
    (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2) (a b : ℕ) :
    (𝟙 (TripleCross.Constructions.chains k X.1.1 ⊗ TripleCross.Constructions.chains k X.1.2) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.2 C).f a ≫ (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
          (tripleSupportComplement X A B C)).f b = 0 := by
  let f : ((X.1.1, X.1.2), TopCat.of C) ⟶ X :=
    ((𝟙 X.1.1, 𝟙 X.1.2), Geometric.LocalHomology.Cycles.subspaceInclusion X.2 C)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inr x.2.property
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id, id_tensorHom_id] using
    associativity_map_into_subspace_zero k f (tripleSupportComplement X A B C) hf a b

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport
