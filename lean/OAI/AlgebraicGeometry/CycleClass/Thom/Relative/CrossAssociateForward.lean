import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity
import OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains

/-! # Cross Associate Forward -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward

/-! Associativity of the original relative homology cross product, with
explicit output degree and the genuine reassociation map of pairs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.TripleCross.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions.Products OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductAssociativity.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions

namespace Constructions.HomologyAssociativity

variable (k : Type) [Field k]

def relativeCrossClassAt (Y Z : TopCat.{0}) (U : Set Y) (V : Set Z)
    (p q n : ℕ) (hpq : p + q = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y U p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Z V q) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k (TopCat.of (Y × Z)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement Y Z U V) n :=
  HomologyProductAssociativity.Constructions.Products.homologyProduct (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k Y Z U V) p q n hpq a b

theorem relativeCrossClassAt_eq_original (Y Z : TopCat.{0}) (U : Set Y) (V : Set Z)
    (p q : ℕ) (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Y U p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ Z V q) :
    relativeCrossClassAt ℚ Y Z U V p q (p + q) rfl a b =
      HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.relativeHomologyCrossClass Y Z U V p q a b := rfl

variable (X : TripleModels.Constructions.SpaceTriple) (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2)

def nestedHomotopy : Homotopy (CrossAssociativity.Constructions.nestedLeft k X A B C) (CrossAssociativity.Constructions.nestedRight k X A B C) := by
  rw [← CrossAssociativity.Constructions.relativeLeft_eq_nested, ← CrossAssociativity.Constructions.relativeRight_eq_nested]
  exact TripleCross.Constructions.relativeAssociativity k X A B C

theorem relativeCrossClassAt_associative (p q r n : ℕ) (h : (p + q) + r = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.1 A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.2 B q)
    (c : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.2 C r) :
    relativeCrossClassAt k (TopCat.of (X.1.1 × X.1.2)) X.2
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C (p + q) r n h
      (relativeCrossClassAt k X.1.1 X.1.2 A B p q (p + q) rfl a b) c =
      homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).inv (CrossAssociativity.Constructions.rightSupportMapsTo X A B C)) n
        (relativeCrossClassAt k X.1.1 (TopCat.of (X.1.2 × X.2)) A
          (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C) p (q + r) n
          ((Nat.add_assoc p q r).symm.trans h) a
          (relativeCrossClassAt k X.1.2 X.2 B C q r (q + r) rfl b c)) := by
  have hh := HomologyProductAssociativity.Constructions.homologyProduct_associative
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.1 X.1.2 A B)
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k (TopCat.of (X.1.1 × X.1.2)) X.2
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C)
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.2 X.2 B C)
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X.1.1 (TopCat.of (X.1.2 × X.2)) A
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C) ≫
        Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).inv (CrossAssociativity.Constructions.rightSupportMapsTo X A B C))
    p q r n h (nestedHomotopy k X A B C) a b c
  rw [HomologyProductAssociativity.Constructions.Products.homologyProduct_comp] at hh
  exact hh

end Constructions.HomologyAssociativity

end AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward

namespace AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions

/-! Forward reassociation of actual relative cross classes. -/

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AssociativitySupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type) [Field k] (X : TripleModels.Constructions.SpaceTriple)
  (A : Set X.1.1) (B : Set X.1.2) (C : Set X.2)

theorem leftSupportMapsTo :
    Set.MapsTo (TripleCross.Constructions.spaceAssociate X).hom (AssociativitySupport.Constructions.tripleSupportComplement X A B C)
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 (TopCat.of (X.1.2 × X.2)) A
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C)) := by
  intro z hz
  exact hz.elim (fun hab => hab.elim Or.inl (fun hb => Or.inr (Or.inl hb)))
    (fun hc => Or.inr (Or.inr hc))

theorem associate_inverse (n : ℕ) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).inv
        (CrossAssociativity.Constructions.rightSupportMapsTo X A B C)) n ≫
      homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).hom
        (leftSupportMapsTo X A B C)) n = 𝟙 _ := by
  rw [Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp]
  change homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k
    (𝟙 (TopCat.of (X.1.1 × (X.1.2 × X.2))))
    (A := HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 (TopCat.of (X.1.2 × X.2)) A
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C)) (fun _ hx => hx)) n = _
  rw [Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap_id, homologyMap_id]

theorem cross_associate (p q r n : ℕ) (h : (p + q) + r = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.1 A p)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.2 B q)
    (c : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.2 C r) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).hom
        (leftSupportMapsTo X A B C)) n
      (HomologyAssociativity.relativeCrossClassAt k (TopCat.of (X.1.1 × X.1.2)) X.2
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C (p + q) r n h
        (HomologyAssociativity.relativeCrossClassAt k X.1.1 X.1.2 A B p q (p + q) rfl a b) c) =
      HomologyAssociativity.relativeCrossClassAt k X.1.1 (TopCat.of (X.1.2 × X.2)) A
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C) p (q + r) n
        ((Nat.add_assoc p q r).symm.trans h) a
        (HomologyAssociativity.relativeCrossClassAt k X.1.2 X.2 B C q r (q + r) rfl b c) := by
  rw [HomologyAssociativity.relativeCrossClassAt_associative]
  exact ConcreteCategory.congr_hom (associate_inverse k X A B C n) _

theorem cross_associate_at (p q r m n : ℕ) (h₁ : p + q = m) (h₂ : m + r = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.1 A p)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.1.2 B q)
    (c : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X.2 C r) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (TripleCross.Constructions.spaceAssociate X).hom
        (leftSupportMapsTo X A B C)) n
      (HomologyAssociativity.relativeCrossClassAt k (TopCat.of (X.1.1 × X.1.2)) X.2
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.1 X.1.2 A B) C m r n h₂
        (HomologyAssociativity.relativeCrossClassAt k X.1.1 X.1.2 A B p q m h₁ a b) c) =
      HomologyAssociativity.relativeCrossClassAt k X.1.1 (TopCat.of (X.1.2 × X.2)) A
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X.1.2 X.2 B C) p (q + r) n
        (by omega) a (HomologyAssociativity.relativeCrossClassAt k X.1.2 X.2 B C q r (q + r) rfl b c) := by
  subst m
  exact cross_associate k X A B C p q r n h₂ a b c

end AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions

end

end OAI
