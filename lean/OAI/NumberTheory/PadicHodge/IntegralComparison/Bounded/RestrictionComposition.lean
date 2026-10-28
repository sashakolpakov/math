import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology

/-! # Restriction Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RestrictionComposition

noncomputable section

/-! Nested geometric restriction of the original bounded crystalline sheaves composes canonically. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (n : ℕ)

local notation "Rg" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Rh" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) h hh n
local notation "Rc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ)
  (g ≫ h) (Crystalline.PostcomposeComposition.overBase g h hg hh) n

def iso : (Rh) ⋙ (Rg) ≅ Rc :=
  Functor.sheafPushforwardContinuousComp'
    (Crystalline.PostcomposeComposition.boundedIso g h hg hh n)
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n) (BoundedCrystalline.Site.topology fZ n)

def objectIso (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fZ n) :
    ((Rh) ⋙ (Rg)).obj M ≅ (Rc).obj M := (iso g h hg hh n).app M

theorem component (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fZ n)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)ᵒᵖ) :
    (objectIso g h hg hh n M).hom.hom.app U =
      M.obj.map ((Crystalline.PostcomposeComposition.boundedIso g h hg hh n).inv.app U.unop).op :=
  Category.id_comp _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RestrictionComposition
