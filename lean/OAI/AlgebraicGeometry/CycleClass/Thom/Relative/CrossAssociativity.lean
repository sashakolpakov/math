import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCross
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossProduct

/-! # Cross Associativity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity

noncomputable section

/-! Identify the descended comparison with the two existing nested relative
cross products, including the actual reassociation map of pairs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleChainQuotient.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions

namespace Constructions

variable (k : Type) [Field k]
variable (X : TripleModels.Constructions.SpaceTriple) (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2)

theorem singularChainCross_eq (Y Z : TopCat.{0}) : HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k Y Z = TripleCross.Constructions.cross k Y Z := rfl

@[reassoc]
theorem relativeCross_projection (Y Z : TopCat.{0}) (U : Set Y) (V : Set Z) :
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y U ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Z V) ≫
      HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k Y Z U V = HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k Y Z ≫
        Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (Y × Z)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z U V) :=
  HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_projection k Y Z U V

def nestedLeft : TripleCross.Constructions.relativeTripleTensor k X A B C ⟶ TripleCross.Constructions.relativeTripleTarget k X A B C :=
  (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.1 X.1.2 A B ⊗ₘ 𝟙 (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.2 C)) ≫
    HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k (TopCat.of (X.1.1 × X.1.2)) X.2
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C

theorem rightSupportMapsTo :
    Set.MapsTo (TripleCross.Constructions.spaceAssociate X).inv
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 (TopCat.of (X.1.2 × X.2)) A
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C)) (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  intro z hz
  exact hz.elim (fun ha => Or.inl (Or.inl ha))
    (fun hbc => hbc.elim (fun hb => Or.inl (Or.inr hb)) Or.inr)

def nestedRight : TripleCross.Constructions.relativeTripleTensor k X A B C ⟶ TripleCross.Constructions.relativeTripleTarget k X A B C :=
  (α_ (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.1.1 A) (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.1.2 B)
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.2 C)).hom ≫
      (𝟙 (Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X.1.1 A) ⊗ₘ HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.2 X.2 B C) ≫
        HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.1 (TopCat.of (X.1.2 × X.2)) A
          (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C) ≫
            Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).inv (rightSupportMapsTo X A B C)

private theorem leftEquiv_hom_eq : (TripleCross.Constructions.leftEquiv k X).hom =
    (TripleCross.Constructions.cross k X.1.1 X.1.2 ⊗ₘ 𝟙 (TripleCross.Constructions.chains k X.2)) ≫
      TripleCross.Constructions.cross k (TopCat.of (X.1.1 × X.1.2)) X.2 := rfl

theorem nestedLeft_projection :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ nestedLeft k X A B C =
      (TripleCross.Constructions.leftEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  rw [nestedLeft, leftEquiv_hom_eq, ← Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id, HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_projection]
  rw [← Category.id_comp (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C), ← tensorHom_comp_tensorHom,
    Category.assoc]
  erw [HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_projection k (TopCat.of (X.1.1 × X.1.2)) X.2
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C]
  rw [singularChainCross_eq, singularChainCross_eq, ← Category.assoc]
  rfl

private theorem nestedRight_projection_explicit :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ nestedRight k X A B C =
      (α_ (TripleCross.Constructions.chains k X.1.1) (TripleCross.Constructions.chains k X.1.2) (TripleCross.Constructions.chains k X.2)).hom ≫
        (𝟙 (TripleCross.Constructions.chains k X.1.1) ⊗ₘ HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X.1.2 X.2) ≫
          HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.singularChainCross k X.1.1 (TopCat.of (X.1.2 × X.2)) ≫
            (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains k).map (TripleCross.Constructions.spaceAssociate X).inv ≫
              Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
                (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  rw [nestedRight, ← Category.assoc, associator_naturality, Category.assoc]
  rw [← Category.assoc (_ ⊗ₘ _), tensorHom_comp_tensorHom, Category.comp_id,
    HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_projection]
  rw [← Category.id_comp (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A), ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  erw [relativeCross_projection_assoc k X.1.1 (TopCat.of (X.1.2 × X.2))
    A (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C)]
  erw [Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality k (TripleCross.Constructions.spaceAssociate X).inv (rightSupportMapsTo X A B C)]
  rfl

theorem nestedRight_projection :
    ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) ≫ nestedRight k X A B C =
      (TripleCross.Constructions.rightEquiv k X).hom ≫ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TripleModels.Constructions.tripleSpace.obj X)
        (AssociativitySupport.Constructions.tripleSupportComplement X A B C) := by
  rw [nestedRight_projection_explicit, TripleCross.Constructions.rightEquiv_hom_eq]
  simp only [singularChainCross_eq, Category.assoc]

theorem tripleProjection_epi :
    Epi ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
      Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) :=
  HomologicalComplex.epi_of_epi_f _ (fun n => TripleChainQuotient.Constructions.tripleQuotient_degree_epi
    (TripleCross.Constructions.factorSequence k X.1.1 A) (TripleCross.Constructions.factorSequence k X.1.2 B) (TripleCross.Constructions.factorSequence k X.2 C)
    (TripleCross.Constructions.factorSequence_shortExact k X.1.1 A) (TripleCross.Constructions.factorSequence_shortExact k X.1.2 B)
    (TripleCross.Constructions.factorSequence_shortExact k X.2 C) n)

theorem relativeLeft_eq_nested : TripleCross.Constructions.relativeLeft k X A B C = nestedLeft k X A B C := by
  let : Epi ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) := tripleProjection_epi k X A B C
  apply (cancel_epi ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C)).mp
  exact (TripleCross.Constructions.relativeLeft_projection k X A B C).trans (nestedLeft_projection k X A B C).symm

theorem relativeRight_eq_nested : TripleCross.Constructions.relativeRight k X A B C = nestedRight k X A B C := by
  let : Epi ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C) := tripleProjection_epi k X A B C
  apply (cancel_epi ((Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.1 A ⊗ₘ
    Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.1.2 B) ⊗ₘ Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X.2 C)).mp
  exact (TripleCross.Constructions.relativeRight_projection k X A B C).trans (nestedRight_projection k X A B C).symm

theorem relative_cross_associative_homology (n : ℕ) :
    homologyMap (nestedLeft k X A B C) n = homologyMap (nestedRight k X A B C) n := by
  rw [← relativeLeft_eq_nested, ← relativeRight_eq_nested]
  exact (TripleCross.Constructions.relativeAssociativity k X A B C).homologyMap_eq n

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity
