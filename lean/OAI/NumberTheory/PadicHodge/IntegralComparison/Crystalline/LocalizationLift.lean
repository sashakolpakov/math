import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps

/-! # Localization Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift

noncomputable section

/-!
# IntegralComparison: the universal property of a principal crystalline localization

A crystalline morphism factors through the principal localization exactly
when the chosen function becomes a unit. The factorization is unique.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U W : BigCrystallineSite.Object p B J δ f} (β : W ⟶ U) (r : U.ring) (hr : IsUnit (β.ringMap r))

def liftRingMap : Localization.Ring U r →+* W.ring :=
  IsLocalization.Away.lift (g := β.ringMap.toRingHom) r hr

lemma liftRingMap_comp : (liftRingMap β r hr).comp (algebraMap U.ring (Localization.Ring U r)) =
    β.ringMap.toRingHom := IsLocalization.Away.lift_comp r hr

def liftDP : DividedPowers.DPMorphism (Localization.dividedPowers U r) W.dividedPowers :=
  DividedPower.Localization.mapFromLocalization U.dividedPowers
    (Submonoid.powers r) (Localization.Ring U r) W.dividedPowers (liftRingMap β r hr) (by
      rw [liftRingMap_comp]
      exact β.ringMap.isDPMorphism)

lemma liftDP_comp : (liftDP β r hr).comp (Localization.localizationDP U r) = β.ringMap := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (liftRingMap_comp β r hr) x

private lemma quotient_comp :
    (BigCrystallineSite.Object.quotientMap W (Localization.object U r) (liftDP β r hr)).comp
      (BigCrystallineSite.Object.quotientMap (Localization.object U r) U (Localization.localizationDP U r)) = BigCrystallineSite.Object.quotientMap W U β.ringMap := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, liftDP_comp]

def liftHom : W ⟶ Localization.object U r where
  ringMap := liftDP β r hr
  overBase := by
    change (liftRingMap β r hr).comp ((algebraMap U.ring (Localization.Ring U r)).comp U.base) = W.base
    rw [← RingHom.comp_assoc, liftRingMap_comp, β.overBase]
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W (Localization.object U r) (liftDP β r hr))) ≫
      (Localization.closedMap U r ≫ U.mapToX) = W.mapToX
    rw [← Category.assoc]
    have hq : Spec.map (CommRingCat.ofHom
          (BigCrystallineSite.Object.quotientMap W (Localization.object U r) (liftDP β r hr))) ≫ Localization.closedMap U r =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W U β.ringMap)) := by
      change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W (Localization.object U r) (liftDP β r hr))) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (Localization.object U r) U (Localization.localizationDP U r))) = _
      rw [← Spec.map_comp]
      exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (quotient_comp β r hr)
    rw [hq]
    exact β.overX

lemma liftHom_comp : liftHom β r hr ≫ Localization.hom U r = β := by
  apply BigCrystallineSite.Object.Hom.ext
  exact liftDP_comp β r hr

lemma liftHom_unique (γ : W ⟶ Localization.object U r) (hγ : γ ≫ Localization.hom U r = β) : γ = liftHom β r hr := by
  apply BigCrystallineSite.Object.Hom.ext
  have he : γ.ringMap.toRingHom = (liftHom β r hr).ringMap.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    exact congrArg (fun t : W ⟶ U => t.ringMap.toRingHom) (hγ.trans (liftHom_comp β r hr).symm)
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun he x

include hr in
lemma existsUnique_factorization : ∃! γ : W ⟶ Localization.object U r, γ ≫ Localization.hom U r = β :=
  ⟨liftHom β r hr, liftHom_comp β r hr, fun γ hγ => liftHom_unique β r hr γ hγ⟩

instance localization_mono (U : BigCrystallineSite.Object p B J δ f) (r : U.ring) : Mono (Localization.hom U r) where
  right_cancellation {Z} a b h := by
    apply BigCrystallineSite.Object.Hom.ext
    have he : a.ringMap.toRingHom = b.ringMap.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers r)
      exact congrArg (fun t : Z ⟶ U => t.ringMap.toRingHom) h
    apply DFunLike.ext
    intro x
    exact DFunLike.congr_fun he x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationLift
