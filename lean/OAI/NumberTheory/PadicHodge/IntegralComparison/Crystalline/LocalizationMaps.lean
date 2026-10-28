import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

/-! # Localization Maps -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps

noncomputable section

/-!
# IntegralComparison: restricting crystalline morphisms to principal opens

The ring map on principal localizations is an actual divided-power map,
and its square with the original crystalline morphism commutes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (r : V.ring)

def ringMap : Crystalline.Localization.Ring V r →+* Crystalline.Localization.Ring U (α.ringMap r) := Localization.awayMap α.ringMap.toRingHom r

lemma ringMap_comp : (LocalizationMaps.ringMap α r).comp (algebraMap V.ring (Crystalline.Localization.Ring V r)) =
    (algebraMap U.ring (Crystalline.Localization.Ring U (α.ringMap r))).comp α.ringMap.toRingHom := by
  unfold LocalizationMaps.ringMap Localization.awayMap IsLocalization.Away.map
  apply IsLocalization.map_comp

def dpMap : DividedPowers.DPMorphism (Crystalline.Localization.dividedPowers V r) (Crystalline.Localization.dividedPowers U (α.ringMap r)) :=
  DividedPower.Localization.mapFromLocalization V.dividedPowers
    (Submonoid.powers r) (Crystalline.Localization.Ring V r) (Crystalline.Localization.dividedPowers U (α.ringMap r)) (LocalizationMaps.ringMap α r) (by
      rw [ringMap_comp]
      exact (Crystalline.Localization.localizationDP U (α.ringMap r)).isDPMorphism.comp _ α.ringMap.isDPMorphism)

lemma dpMap_comp : (dpMap α r).comp (Crystalline.Localization.localizationDP V r) =
    (Crystalline.Localization.localizationDP U (α.ringMap r)).comp α.ringMap := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (ringMap_comp α r) x

private lemma quotient_comp :
    (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) (Crystalline.Localization.object V r) (dpMap α r)).comp
        (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object V r) V (Crystalline.Localization.localizationDP V r)) =
      (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) U (Crystalline.Localization.localizationDP U (α.ringMap r))).comp
        (BigCrystallineSite.Object.quotientMap U V α.ringMap) := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, ← BigCrystallineSite.Object.quotientMap_comp, dpMap_comp]

lemma closed_square :
    Spec.map (CommRingCat.ofHom
      (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) (Crystalline.Localization.object V r) (dpMap α r))) ≫ Crystalline.Localization.closedMap V r =
    Crystalline.Localization.closedMap U (α.ringMap r) ≫ Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)) := by
  change Spec.map (CommRingCat.ofHom
        (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) (Crystalline.Localization.object V r) (dpMap α r))) ≫
      Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object V r) V (Crystalline.Localization.localizationDP V r))) =
    Spec.map (CommRingCat.ofHom
        (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) U (Crystalline.Localization.localizationDP U (α.ringMap r)))) ≫
      Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap))
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (quotient_comp α r)

def localizedHom : Crystalline.Localization.object U (α.ringMap r) ⟶ Crystalline.Localization.object V r where
  ringMap := dpMap α r
  overBase := by
    change (LocalizationMaps.ringMap α r).comp ((algebraMap V.ring (Crystalline.Localization.Ring V r)).comp V.base) =
      (algebraMap U.ring (Crystalline.Localization.Ring U (α.ringMap r))).comp U.base
    rw [← RingHom.comp_assoc, ringMap_comp, RingHom.comp_assoc, α.overBase]
  overX := by
    change Spec.map (CommRingCat.ofHom
        (BigCrystallineSite.Object.quotientMap (Crystalline.Localization.object U (α.ringMap r)) (Crystalline.Localization.object V r) (dpMap α r))) ≫
      (Crystalline.Localization.closedMap V r ≫ V.mapToX) = Crystalline.Localization.closedMap U (α.ringMap r) ≫ U.mapToX
    rw [← Category.assoc, closed_square, Category.assoc, α.overX]

lemma localizedHom_square : localizedHom α r ≫ Crystalline.Localization.hom V r = Crystalline.Localization.hom U (α.ringMap r) ≫ α := by
  apply BigCrystallineSite.Object.Hom.ext
  exact dpMap_comp α r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalizationMaps
