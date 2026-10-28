import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.MonomorphismProducts

/-! # Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

noncomputable section

/-!
# IntegralComparison: the bounded crystalline category of a chart is its actual geometric subcategory
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

def postcompose : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤
    BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n :=
  (BoundedCrystalline.Site.property fY n).lift
    (BoundedCrystalline.Site.inclusion f n ⋙ BigCrystallineSite.postcompose g hg) (fun U => U.property)

instance postcompose_faithful : (postcompose (p := p) (J := J) (δ := δ) g hg n).Faithful where
  map_injective {U V} {α β} h := by
    apply (BoundedCrystalline.Site.inclusion f n).map_injective
    apply (BigCrystallineSite.postcompose g hg).map_injective
    exact congrArg (fun t : (postcompose g hg n).obj U ⟶ (postcompose g hg n).obj V => t.hom) h

def openFunctor : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ⥤
    Subsite.Objects (p := p) (J := J) (δ := δ) fY g n :=
  (Subsite.property fY g n).lift (postcompose g hg n) (fun U => ⟨U.obj.mapToX, rfl⟩)

instance openFunctor_faithful : (openFunctor (p := p) (J := J) (δ := δ) g hg n).Faithful where
  map_injective {U V} {α β} h := by
    apply (postcompose g hg n).map_injective
    exact congrArg (fun t : (openFunctor g hg n).obj U ⟶ (openFunctor g hg n).obj V => t.hom) h

instance openFunctor_essSurj : (openFunctor (p := p) (J := J) (δ := δ) g hg n).EssSurj := by
  refine ⟨?_⟩
  intro U
  obtain ⟨t, ht⟩ := U.property
  let V : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n :=
    ⟨Crystalline.OpenCondition.liftObject g hg U.obj.obj t ht, U.obj.property⟩
  refine ⟨V, ⟨?_⟩⟩
  exact (Subsite.property fY g n).isoMk
    ((BoundedCrystalline.Site.property fY n).isoMk (Crystalline.OpenCondition.liftIso g hg U.obj.obj t ht))

variable [Mono g]

instance postcompose_full : (postcompose (p := p) (J := J) (δ := δ) g hg n).Full where
  map_surjective α := by
    refine ⟨ObjectProperty.homMk (Crystalline.MonomorphismProducts.preimage g hg α.hom), ?_⟩
    apply (BoundedCrystalline.Site.inclusion fY n).map_injective
    apply BigCrystallineSite.Object.Hom.ext
    rfl

instance openFunctor_full : (openFunctor (p := p) (J := J) (δ := δ) g hg n).Full where
  map_surjective α := by
    refine ⟨(postcompose g hg n).preimage α.hom, ?_⟩
    apply (Subsite.inclusion fY g n).map_injective
    exact (postcompose g hg n).map_preimage α.hom

instance openFunctor_isEquivalence : (openFunctor (p := p) (J := J) (δ := δ) g hg n).IsEquivalence := {}

def equivalence : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n ≌
    Subsite.Objects (p := p) (J := J) (δ := δ) fY g n :=
  (openFunctor g hg n).asEquivalence

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence
