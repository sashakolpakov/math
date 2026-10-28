import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorChainQuotient
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Relative Cross Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions

noncomputable section

/-!
# DegreeTwo: the actual relative singular chain cross product

The product is descended from the previously constructed natural
Eilenberg–Zilber map. Its defining identity fixes its value on every pair
of quotient representatives and makes the construction independent of
all representatives.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false

variable (k : Type) [Field k]

def relativeSingularChainCross (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k Y B ⟶
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) :=
  TensorChainQuotient.Constructions.tensorChainQuotientDesc (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence k X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence k Y B)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact k X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact k Y B)
    (RelativeCrossSupport.Constructions.singularChainCross k X Y ≫
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B))
    (RelativeCrossSupport.Constructions.singularChainCross_left_zero k X Y A B) (RelativeCrossSupport.Constructions.singularChainCross_right_zero k X Y A B)

theorem relativeSingularChainCross_projection (X Y : TopCat.{0}) (A : Set X) (B : Set Y) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B) ≫
        relativeSingularChainCross k X Y A B =
      RelativeCrossSupport.Constructions.singularChainCross k X Y ≫
        CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) :=
  TensorChainQuotient.Constructions.tensorChainQuotientDesc_fac (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence k X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence k Y B)
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact k X A) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact k Y B)
    (RelativeCrossSupport.Constructions.singularChainCross k X Y ≫
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B))
    (RelativeCrossSupport.Constructions.singularChainCross_left_zero k X Y A B) (RelativeCrossSupport.Constructions.singularChainCross_right_zero k X Y A B)

theorem crossSupportComplement_mapsTo
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    {A : Set X} {A' : Set X'} {B : Set Y} {B' : Set Y'}
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') :
    Set.MapsTo (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
      (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) (RelativeCrossSupport.Constructions.crossSupportComplement X' Y' A' B') := by
  intro x hx
  exact hx.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hg h))

/-- Naturality holds for the actual relative maps in both factors. -/
theorem relativeSingularChainCross_naturality
    {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    {A : Set X} {A' : Set X'} {B : Set Y} {B' : Set Y'}
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k f hf ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k g hg) ≫
        relativeSingularChainCross k X' Y' A' B' =
      relativeSingularChainCross k X Y A B ≫
        CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
          (crossSupportComplement_mapsTo f g hf hg) := by
  have : Epi (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B) :=
    HomologicalComplex.epi_of_epi_f _ (fun n => TensorChainQuotient.Constructions.tensorChainHom_degree_epi _ _ n)
  apply (cancel_epi (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k X A ⊗ₘ
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection k Y B)).mp
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality, CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality,
    ← tensorHom_comp_tensorHom, Category.assoc, relativeSingularChainCross_projection,
    ← Category.assoc, RelativeCrossSupport.Constructions.singularChainCross_naturality, Category.assoc]
  have hn := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality k
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f,g) : (X,Y) ⟶ (X',Y')))
    (crossSupportComplement_mapsTo f g hf hg)
  conv_rhs => rw [← Category.assoc, relativeSingularChainCross_projection, Category.assoc]
  exact congrArg (fun u => RelativeCrossSupport.Constructions.singularChainCross k X Y ≫ u) hn.symm

/-- The chain cross product induces a map on the actual relative
homology of the tensor complex. -/
def relativeSingularCrossHomology (X Y : TopCat.{0}) (A : Set X) (B : Set Y) (n : ℕ) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k X A ⊗ CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains k Y B).homology n ⟶
      CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k (TopCat.of (X × Y)) (RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n :=
  HomologicalComplex.homologyMap (relativeSingularChainCross k X Y A B) n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions
