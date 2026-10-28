import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology

/-! # Level Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps

noncomputable section

/-!
# IntegralComparison: exact restriction between the actual bounded crystalline levels
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

def inclusion : Site.Objects (p := p) (J := J) (δ := δ) f n ⥤ Site.Objects (p := p) (J := J) (δ := δ) f m :=
  ObjectProperty.ιOfLE (fun _ => Site.property_mono f n m hnm)

def incomingLifts : SiteLifts.IncomingLifts (inclusion (p := p) (J := J) (δ := δ) f n m hnm) where
  object {U V} α := ⟨V.obj, Site.property_of_hom f n α.hom U.property⟩
  iso _ := Iso.refl _
  hom α := ObjectProperty.homMk α.hom
  map_hom α := (Category.id_comp α).symm
  fullTriangle _ _ c h := ⟨ObjectProperty.homMk c.hom, rfl, by
    apply (Site.property f n).ι.map_injective
    exact congrArg (fun t => t.hom) h⟩

theorem pushforward_comp {U : Site.Objects (p := p) (J := J) (δ := δ) f n} (S : Sieve U) :
    (S.functorPushforward (inclusion f n m hnm)).functorPushforward (Site.inclusion f m) =
      S.functorPushforward (Site.inclusion f n) :=
  (Sieve.functorPushforward_comp (inclusion f n m hnm) (Site.inclusion f m) S).symm

theorem coverPreserving : CoverPreserving (Site.topology f n) (Site.topology f m)
    (inclusion (p := p) (J := J) (δ := δ) f n m hnm) where
  cover_preserve {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [pushforward_comp]
    exact (CoverPreserving.of_isContinuous (Site.inclusion f n)
      (Site.topology f n) BigCrystallineSite.Object.topology).cover_preserve hS

instance continuous : (inclusion (p := p) (J := J) (δ := δ) f n m hnm).IsContinuous
    (Site.topology f n) (Site.topology f m) :=
  Functor.isContinuous_of_coverPreserving
    ((incomingLifts f n m hnm).compatiblePreserving (Site.topology f m)) (coverPreserving f n m hnm)

theorem pushforward_pullback {U : Site.Objects (p := p) (J := J) (δ := δ) f n}
    (S : Sieve ((inclusion f n m hnm).obj U)) :
    (S.functorPullback (inclusion f n m hnm)).functorPushforward (inclusion f n m hnm) = S := by
  refine le_antisymm (Sieve.functorPullback_pushforward_le _ _) ?_
  intro V α hα
  exact ⟨⟨V.obj, Site.property_of_hom f n α.hom U.property⟩, ObjectProperty.homMk α.hom,
    𝟙 V, hα, (Category.id_comp α).symm⟩

instance cocontinuous : (inclusion (p := p) (J := J) (δ := δ) f n m hnm).IsCocontinuous
    (Site.topology f n) (Site.topology f m) where
  cover_lift {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [← pushforward_comp f n m hnm, pushforward_pullback]
    exact (CoverPreserving.of_isContinuous (Site.inclusion f m)
      (Site.topology f m) BigCrystallineSite.Object.topology).cover_preserve hS

abbrev restriction : Site.ModuleSheaf (p := p) (J := J) (δ := δ) f m ⥤
    Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (inclusion f n m hnm).sheafPushforwardContinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (Site.topology f n) (Site.topology f m)

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) f n m hnm).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) (J := J) (δ := δ) f n m hnm).Linear (Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) f n m hnm).IsLeftAdjoint :=
  ((inclusion f n m hnm).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (Site.topology f n) (Site.topology f m)).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) f n m hnm) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) f n m hnm) := by infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps
