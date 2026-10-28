import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward
import OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductNaturality

/-! # Cross Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality

noncomputable section

/-! Naturality and scalar formulas for the actual relative cross classes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity
open OAI.AlgebraicGeometry.CycleClass.Thom.HomologyProductNaturality.Constructions

namespace Constructions

variable (k : Type) [Field k]
variable {X Y X' Y' : TopCat.{0}} {A : Set X} {B : Set Y} {A' : Set X'} {B' : Set Y'}

theorem relativeCrossClassAt_natural (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (p q n : ℕ) (hpq : p + q = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
      (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg)) n
      (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b) =
        CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X' Y' A' B' p q n hpq
          (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k f hf) p a)
          (homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k g hg) q b) :=
  HomologyProductNaturality.Constructions.homologyProduct_natural (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X Y A B)
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X' Y' A' B')
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k f hf) (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k g hg)
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap k (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y')))
      (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg))
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross_naturality k f g hf hg) p q n hpq a b

theorem relativeCrossClassAt_smul_left (p q n : ℕ) (hpq : p + q = n) (s : k)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq (s • a) b =
      s • CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b :=
  HomologyProductNaturality.Constructions.homologyProduct_smul_left (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X Y A B) p q n hpq s a b

theorem relativeCrossClassAt_smul_right (p q n : ℕ) (hpq : p + q = n) (s : k)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a (s • b) =
      s • CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b :=
  HomologyProductNaturality.Constructions.homologyProduct_smul_right (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X Y A B) p q n hpq s a b

theorem relativeCrossClassAt_cast (p q n : ℕ) (hpq : p + q = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k X A p) (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k Y B q) :
    CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q n hpq a b =
      eqToHom (congrArg (fun j => Geometric.RelativeScalarChains.Cycles.relativeScalarHomology k (TopCat.of (X × Y))
        (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) j) hpq)
        (CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt k X Y A B p q (p + q) rfl a b) :=
  HomologyProductNaturality.Constructions.homologyProduct_cast (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross k X Y A B) p q n hpq a b

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality
