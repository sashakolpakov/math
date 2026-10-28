import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiInverseImage
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Zariski Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiAdjunction

noncomputable section

/-!
# IntegralComparison: the original bounded crystalline Zariski image preserves injectives
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def presheafAdjunction : ZariskiInverseImage.presheaves (p := p) (J := J) (δ := δ) fY n ⊣
    Incoming.SectionPresheaf.functor (Crystalline.ExactRestriction.Coeff (B := B)) (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedOpen.SectionPresheaf.property fY n) (BoundedOpen.SectionPresheaf.monotone fY n) :=
  NeighborhoodAdjunction.adjunction (Crystalline.ExactRestriction.Coeff (B := B))
    (BoundedOpen.SectionPresheaf.property fY n) (BoundedOpen.SectionPresheaf.monotone fY n)
    (fun V {_ _} α => BoundedOpen.SectionPresheaf.incoming fY n V α)

def adjunction : ZariskiInverseImage.sheaves (p := p) (J := J) (δ := δ) fY n ⊣
    BoundedOpen.SectionSheaf.functor fY n :=
  Adjunction.restrictFullyFaithful
    ((presheafAdjunction (p := p) (J := J) (δ := δ) fY n).comp
      (sheafificationAdjunction (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))))
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance preservesInjectiveObjects :
    (BoundedOpen.SectionSheaf.functor (p := p) (J := J) (δ := δ) fY n).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction fY n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiAdjunction
