import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization

/-! # Crystalline Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallinePullback

noncomputable section

/-!
# IntegralComparison: principal pullbacks in the original small crystalline site
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineLocalization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : Crystalline.Site.AffineThickening p B J δ f} (α : U ⟶ V) (r : V.ring)

def smallLocalizedHom : CrystallineLocalization.smallObject U (α.ringMap r) ⟶ CrystallineLocalization.smallObject V r :=
  BigCrystallineSite.fromSmall.preimage (Crystalline.LocalizationMaps.localizedHom (BigCrystallineSite.fromSmall.map α) r)

lemma smallLocalizedHom_map : BigCrystallineSite.fromSmall.map (smallLocalizedHom α r) =
    Crystalline.LocalizationMaps.localizedHom (BigCrystallineSite.fromSmall.map α) r := Functor.map_preimage _ _

lemma small_principal_pullback :
    IsPullback (smallLocalizedHom α r) (CrystallineLocalization.smallHom U (α.ringMap r)) (CrystallineLocalization.smallHom V r) α := by
  apply IsPullback.of_map_of_faithful BigCrystallineSite.fromSmall
  rw [smallLocalizedHom_map, CrystallineLocalization.fromSmall_smallHom, CrystallineLocalization.fromSmall_smallHom]
  exact CrystallinePrincipal.PrincipalPullback.principal_pullback (BigCrystallineSite.fromSmall.map α) r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallinePullback
