import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Postcompose Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeLifts

noncomputable section

/-!
# IntegralComparison: incoming morphisms lift along actual bounded crystalline postcomposition
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

def incomingLifts : SiteLifts.IncomingLifts
    (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n) where
  object {U V} α := ⟨Crystalline.Lifts.liftedObject g hg α.hom, V.property⟩
  iso α := (BoundedCrystalline.Site.property fY n).isoMk (Crystalline.Lifts.liftedIso g hg α.hom)
  hom α := ObjectProperty.homMk (Crystalline.Lifts.liftedHom g hg α.hom)
  map_hom α := by
    apply (BoundedCrystalline.Site.inclusion fY n).map_injective
    exact Crystalline.Lifts.liftedHom_map g hg α.hom
  fullTriangle {U V W} a b c h := by
    have h' : c.hom ≫ (BigCrystallineSite.postcompose g hg).map b.hom =
        (BigCrystallineSite.postcompose g hg).map a.hom :=
      congrArg (fun t => t.hom) h
    refine ⟨ObjectProperty.homMk (Crystalline.Lifts.liftTriangle g hg a.hom b.hom c.hom h'), ?_, ?_⟩
    · apply (BoundedCrystalline.Site.inclusion fY n).map_injective
      exact Crystalline.Lifts.liftTriangle_map g hg a.hom b.hom c.hom h'
    · apply (BoundedCrystalline.Site.inclusion f n).map_injective
      exact Crystalline.Lifts.liftTriangle_comp g hg a.hom b.hom c.hom h'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeLifts
