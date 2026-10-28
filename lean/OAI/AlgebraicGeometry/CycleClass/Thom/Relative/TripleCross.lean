import OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport
import OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotientHomotopy

/-! # Triple Cross -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCross

noncomputable section

/-! Descend the two actual iterated cross maps and their natural homotopy
through the three relative factor quotients. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.NaturalAssociativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotientHomotopy.Constructions

namespace Constructions

variable (k : Type) [Field k]

abbrev factorSequence (Y : TopCat.{0}) (U : Set Y) :
    ShortComplex (ChainComplex (ModuleCat.{0} k) ℕ) :=
  ShortComplex.mk (X₁ := TripleCross.Constructions.chains k (TopCat.of U)) (X₂ := TripleCross.Constructions.chains k Y)
    (X₃ := Geometric.RelativeScalarChains.Cycles.relativeScalarChains k Y U) (Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k Y U)
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y U) (Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection k Y U)

theorem factorSequence_shortExact (Y : TopCat.{0}) (U : Set Y) :
    (factorSequence k Y U).ShortExact := Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact k Y U

variable (φ : ∀ X : TripleModels.Constructions.SpaceTriple, TripleCross.Constructions.tensorTriple k X ⟶ (TripleModels.Constructions.tripleChainFunctor k).obj X)
variable (hφ : ∀ {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y),
  TripleCross.Constructions.tensorTripleMap k f ≫ φ Y = φ X ≫ (TripleModels.Constructions.tripleChainFunctor k).map f)

include hφ in
theorem map_into_subspace_zero {X Y : TripleModels.Constructions.SpaceTriple} (f : X ⟶ Y)
    (U : Set (TripleModels.Constructions.tripleSpace.obj Y)) (hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ U) :
    TripleCross.Constructions.tensorTripleMap k f ≫ φ Y ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj Y) U = 0 := by
  have hz := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.scalarChainMap_relativeProjection_zero k (TripleModels.Constructions.tripleSpace.map f) U hf
  change (TripleModels.Constructions.tripleChainFunctor k).map f ≫
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj Y) U = 0 at hz
  rw [← Category.assoc, hφ, Category.assoc, hz, comp_zero]

variable (X : TripleModels.Constructions.SpaceTriple) (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2)

include hφ in
theorem map_first_zero :
    ((Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.1 A ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.1.2)) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)) ≫ φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) = 0 := by
  let f : ((TopCat.of A, X.1.2), X.2) ⟶ X :=
    ((Geometric.LocalHomology.Cycles.subspaceInclusion X.1.1 A, 𝟙 X.1.2), 𝟙 X.2)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ AssociativitySupport.Constructions.tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inl (Or.inl x.1.1.property)
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id] using
    map_into_subspace_zero k φ hφ f (AssociativitySupport.Constructions.tripleSupportComplement X A B C) hf

include hφ in
theorem map_second_zero :
    ((𝟙 (TripleCross.Constructions.chains k X.1.1) ⊗ₘ Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.2 B) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)) ≫ φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) = 0 := by
  let f : ((X.1.1, TopCat.of B), X.2) ⟶ X :=
    ((𝟙 X.1.1, Geometric.LocalHomology.Cycles.subspaceInclusion X.1.2 B), 𝟙 X.2)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ AssociativitySupport.Constructions.tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inl (Or.inr x.1.2.property)
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id] using
    map_into_subspace_zero k φ hφ f (AssociativitySupport.Constructions.tripleSupportComplement X A B C) hf

include hφ in
theorem map_third_zero :
    (𝟙 (TripleCross.Constructions.chains k X.1.1 ⊗ TripleCross.Constructions.chains k X.1.2) ⊗ₘ Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.2 C) ≫
      φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) = 0 := by
  let f : ((X.1.1, X.1.2), TopCat.of C) ⟶ X :=
    ((𝟙 X.1.1, 𝟙 X.1.2), Geometric.LocalHomology.Cycles.subspaceInclusion X.2 C)
  have hf : Set.range (TripleModels.Constructions.tripleSpace.map f) ⊆ AssociativitySupport.Constructions.tripleSupportComplement X A B C := by
    rintro _ ⟨x, rfl⟩
    exact Or.inr x.2.property
  simpa only [TripleCross.Constructions.tensorTripleMap, f, CategoryTheory.Functor.map_id, id_tensorHom_id] using
    map_into_subspace_zero k φ hφ f (AssociativitySupport.Constructions.tripleSupportComplement X A B C) hf

abbrev relativeTripleTensor :=
  (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.1.1 A ⊗ Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.1.2 B) ⊗
    Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.2 C

abbrev relativeTripleTarget :=
  Geometric.RelativeScalarChains.Cycles.relativeScalarChains k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C)

def relativeTripleMap : relativeTripleTensor k X A B C ⟶ relativeTripleTarget k X A B C :=
  TripleChainQuotient.Constructions.tripleChainQuotientDesc
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B)
    (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C)
    (φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C))
    (map_first_zero k φ hφ X A B C) (map_second_zero k φ hφ X A B C)
    (map_third_zero k φ hφ X A B C)

theorem relativeTripleMap_projection :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ relativeTripleMap k φ hφ X A B C =
      φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C) :=
  TripleChainQuotient.Constructions.tripleChainQuotientDesc_fac
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B)
    (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C)
    (φ X ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C))
    (map_first_zero k φ hφ X A B C) (map_second_zero k φ hφ X A B C)
    (map_third_zero k φ hφ X A B C)

def relativeLeft : relativeTripleTensor k X A B C ⟶ relativeTripleTarget k X A B C :=
  relativeTripleMap k (fun Y => (TripleCross.Constructions.leftEquiv k Y).hom)
    (fun {_Y _Z} f => TripleCross.Constructions.leftEquiv_hom_natural k f) X A B C

def relativeRight : relativeTripleTensor k X A B C ⟶ relativeTripleTarget k X A B C :=
  relativeTripleMap k (fun Y => (TripleCross.Constructions.rightEquiv k Y).hom)
    (fun {_Y _Z} f => TripleCross.Constructions.rightEquiv_hom_natural k f) X A B C

theorem relativeLeft_projection :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ relativeLeft k X A B C =
      (TripleCross.Constructions.leftEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  simpa only [relativeLeft] using relativeTripleMap_projection k (fun Y => (TripleCross.Constructions.leftEquiv k Y).hom)
    (fun {_Y _Z} f => TripleCross.Constructions.leftEquiv_hom_natural k f) X A B C

theorem relativeRight_projection :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ relativeRight k X A B C =
      (TripleCross.Constructions.rightEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  simpa only [relativeRight] using relativeTripleMap_projection k (fun Y => (TripleCross.Constructions.rightEquiv k Y).hom)
    (fun {_Y _Z} f => TripleCross.Constructions.rightEquiv_hom_natural k f) X A B C

def projectedAssociativity :
    Homotopy ((TripleCross.Constructions.leftEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
      (AssociativitySupport.Constructions.tripleSupportComplement X A B C))
      ((TripleCross.Constructions.rightEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C)) :=
  (Tensor.NaturalAssociativity.Constructions.associativity k X).compRight (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
    (AssociativitySupport.Constructions.tripleSupportComplement X A B C))

theorem projectedAssociativity_first_zero (a b : ℕ) :
    ((Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.1 A ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.1.2)) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)).f a ≫ (projectedAssociativity k X A B C).hom a b = 0 :=
  AssociativitySupport.Constructions.associativity_first_zero k X A B C a b

theorem projectedAssociativity_second_zero (a b : ℕ) :
    ((𝟙 (TripleCross.Constructions.chains k X.1.1) ⊗ₘ Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.1.2 B) ⊗ₘ
      𝟙 (TripleCross.Constructions.chains k X.2)).f a ≫ (projectedAssociativity k X A B C).hom a b = 0 :=
  AssociativitySupport.Constructions.associativity_second_zero k X A B C a b

theorem projectedAssociativity_third_zero (a b : ℕ) :
    (𝟙 (TripleCross.Constructions.chains k X.1.1 ⊗ TripleCross.Constructions.chains k X.1.2) ⊗ₘ Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion k X.2 C).f a ≫
      (projectedAssociativity k X A B C).hom a b = 0 :=
  AssociativitySupport.Constructions.associativity_third_zero k X A B C a b

theorem factor_first_zero (a b : ℕ) :
    (((factorSequence k X.1.1 A).f ⊗ₘ 𝟙 (factorSequence k X.1.2 B).X₂) ⊗ₘ
      𝟙 (factorSequence k X.2 C).X₂).f a ≫ (projectedAssociativity k X A B C).hom a b = 0 := by
  simpa only [factorSequence, TripleCross.Constructions.chains] using projectedAssociativity_first_zero k X A B C a b

theorem factor_second_zero (a b : ℕ) :
    ((𝟙 (factorSequence k X.1.1 A).X₂ ⊗ₘ (factorSequence k X.1.2 B).f) ⊗ₘ
      𝟙 (factorSequence k X.2 C).X₂).f a ≫ (projectedAssociativity k X A B C).hom a b = 0 := by
  simpa only [factorSequence, TripleCross.Constructions.chains] using projectedAssociativity_second_zero k X A B C a b

theorem factor_third_zero (a b : ℕ) :
    (𝟙 ((factorSequence k X.1.1 A).X₂ ⊗ (factorSequence k X.1.2 B).X₂) ⊗ₘ
      (factorSequence k X.2 C).f).f a ≫ (projectedAssociativity k X A B C).hom a b = 0 := by
  simpa only [factorSequence, TripleCross.Constructions.chains] using projectedAssociativity_third_zero k X A B C a b

def relativeHomotopyComponent (a b : ℕ) :
    (relativeTripleTensor k X A B C).X a ⟶ (relativeTripleTarget k X A B C).X b := by
  have K := TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B) (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C) a ((projectedAssociativity k X A B C).hom a b)
    (factor_first_zero k X A B C a b)
    (factor_second_zero k X A B C a b)
    (factor_third_zero k X A B C a b)

  simpa only [relativeTripleTensor, relativeTripleTarget, factorSequence, TripleCross.Constructions.chains] using K

theorem relativeHomotopyComponent_fac (a b : ℕ) :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C).f a ≫ relativeHomotopyComponent k X A B C a b =
      (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫ (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C)).f b :=
  TripleDegreeQuotient.Constructions.tripleDegreeQuotientDesc_fac
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B) (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C) a ((projectedAssociativity k X A B C).hom a b)
    (factor_first_zero k X A B C a b)
    (factor_second_zero k X A B C a b)
    (factor_third_zero k X A B C a b)

theorem relativeHomotopyComponent_zero (a b : ℕ) (hab : ¬ (ComplexShape.down ℕ).Rel b a) :
    relativeHomotopyComponent k X A B C a b = 0 := by
  let π := (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C
  let : Epi (π.f a) := TripleChainQuotient.Constructions.tripleQuotient_degree_epi
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B) (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C) a
  apply (cancel_epi (π.f a)).mp
  rw [relativeHomotopyComponent_fac, (Tensor.NaturalAssociativity.Constructions.associativity k X).zero a b hab, zero_comp, comp_zero]

theorem relativeHomotopyComponent_dNext (n : ℕ) :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C).f n ≫ dNext n (relativeHomotopyComponent k X A B C) =
      dNext n (Tensor.NaturalAssociativity.Constructions.associativity k X).hom ≫ (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C)).f n := by
  let π : TripleCross.Constructions.tensorTriple k X ⟶ relativeTripleTensor k X A B C :=
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C
  let ρ : (TripleModels.Constructions.tripleChainFunctor k).obj X ⟶ relativeTripleTarget k X A B C :=
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C)
  let K := relativeHomotopyComponent k X A B C
  have hK (a b : ℕ) : π.f a ≫ K a b = (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫ ρ.f b :=
    relativeHomotopyComponent_fac k X A B C a b
  calc
    _ = dNext n (fun a b => π.f a ≫ K a b) := (dNext_comp_left π K n).symm
    _ = dNext n (fun a b => (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫ ρ.f b) := by simp only [hK]
    _ = _ := dNext_comp_right (Tensor.NaturalAssociativity.Constructions.associativity k X).hom ρ n

theorem relativeHomotopyComponent_prevD (n : ℕ) :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C).f n ≫ prevD n (relativeHomotopyComponent k X A B C) =
      prevD n (Tensor.NaturalAssociativity.Constructions.associativity k X).hom ≫ (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C)).f n := by
  let π : TripleCross.Constructions.tensorTriple k X ⟶ relativeTripleTensor k X A B C :=
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C
  let ρ : (TripleModels.Constructions.tripleChainFunctor k).obj X ⟶ relativeTripleTarget k X A B C :=
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C)
  let K := relativeHomotopyComponent k X A B C
  have hK (a b : ℕ) : π.f a ≫ K a b = (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫ ρ.f b :=
    relativeHomotopyComponent_fac k X A B C a b
  calc
    _ = prevD n (fun a b => π.f a ≫ K a b) := (prevD_comp_left π K n).symm
    _ = prevD n (fun a b => (Tensor.NaturalAssociativity.Constructions.associativity k X).hom a b ≫ ρ.f b) := by simp only [hK]
    _ = _ := prevD_comp_right (Tensor.NaturalAssociativity.Constructions.associativity k X).hom ρ n

theorem absoluteAssociativity_comm (n : ℕ) :
    (TripleCross.Constructions.leftEquiv k X).hom.f n = dNext n (Tensor.NaturalAssociativity.Constructions.associativity k X).hom +
      prevD n (Tensor.NaturalAssociativity.Constructions.associativity k X).hom + (TripleCross.Constructions.rightEquiv k X).hom.f n :=
  (Tensor.NaturalAssociativity.Constructions.associativity k X).comm n

theorem relativeHomotopyComponent_comm (n : ℕ) :
    (relativeLeft k X A B C).f n =
      dNext n (relativeHomotopyComponent k X A B C) +
        prevD n (relativeHomotopyComponent k X A B C) + (relativeRight k X A B C).f n := by
  let π := (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C
  let ρ := Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X) (AssociativitySupport.Constructions.tripleSupportComplement X A B C)
  let : Epi (π.f n) := TripleChainQuotient.Constructions.tripleQuotient_degree_epi
    (factorSequence k X.1.1 A) (factorSequence k X.1.2 B) (factorSequence k X.2 C)
    (factorSequence_shortExact k X.1.1 A) (factorSequence_shortExact k X.1.2 B)
    (factorSequence_shortExact k X.2 C) n
  have hf : π.f n ≫ (relativeLeft k X A B C).f n = (TripleCross.Constructions.leftEquiv k X).hom.f n ≫ ρ.f n :=
    HomologicalComplex.congr_hom (relativeLeft_projection k X A B C) n
  have hg : π.f n ≫ (relativeRight k X A B C).f n = (TripleCross.Constructions.rightEquiv k X).hom.f n ≫ ρ.f n :=
    HomologicalComplex.congr_hom (relativeRight_projection k X A B C) n
  apply (cancel_epi (π.f n)).mp
  rw [Preadditive.comp_add, Preadditive.comp_add, hf, hg,
    relativeHomotopyComponent_dNext, relativeHomotopyComponent_prevD,
    ← Preadditive.add_comp, ← Preadditive.add_comp]
  rw [← absoluteAssociativity_comm k X n]

def relativeAssociativity : Homotopy (relativeLeft k X A B C) (relativeRight k X A B C) where
  hom := relativeHomotopyComponent k X A B C
  zero := relativeHomotopyComponent_zero k X A B C
  comm := relativeHomotopyComponent_comm k X A B C

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCross
