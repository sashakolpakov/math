import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

/-! # Principal Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalPullback

noncomputable section

/-!
# IntegralComparison: pullbacks of principal open crystalline morphisms

The pullback of localization at r along α is localization at α(r).
The universal property is proved in the crystalline category itself.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (r : V.ring)

lemma cone_unit {Z : BigCrystallineSite.Object p B J δ f} (a : Z ⟶ Crystalline.Localization.object V r) (b : Z ⟶ U)
    (h : a ≫ Crystalline.Localization.hom V r = b ≫ α) : IsUnit (b.ringMap (α.ringMap r)) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit (S := Crystalline.Localization.Ring V r) r).map a.ringMap.toRingHom
  have he := congrArg (fun t : Z ⟶ V => t.ringMap r) h
  change a.ringMap (algebraMap V.ring (Crystalline.Localization.Ring V r) r) = b.ringMap (α.ringMap r) at he
  exact he ▸ hu

lemma principal_pullback :
    IsPullback (Crystalline.LocalizationMaps.localizedHom α r) (Crystalline.Localization.hom U (α.ringMap r)) (Crystalline.Localization.hom V r) α := by
  apply IsPullback.mk' (Crystalline.LocalizationMaps.localizedHom_square α r)
  · intro Z a b _ hab
    exact (cancel_mono (Crystalline.Localization.hom U (α.ringMap r))).mp hab
  · intro Z a b h
    let l := Crystalline.LocalizationLift.liftHom b (α.ringMap r) (cone_unit α r a b h)
    have hl : l ≫ Crystalline.Localization.hom U (α.ringMap r) = b := Crystalline.LocalizationLift.liftHom_comp b _ _
    refine ⟨l, ?_, hl⟩
    apply (cancel_mono (Crystalline.Localization.hom V r)).mp
    rw [Category.assoc, Crystalline.LocalizationMaps.localizedHom_square, ← Category.assoc, hl]
    exact h.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalPullback
