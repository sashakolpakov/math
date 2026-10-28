import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Base Generated -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BaseGenerated.BaseGeneratedFrameLift

noncomputable section

/-! For a frame whose defining ideal comes from the base, every ring
factorization of an incoming crystalline map is already a crystalline map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V T : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (β : T ⟶ V)
  (hgen : U.ideal = J.map U.base) (φ : U.ring →+* T.ring)
  (hφ : φ.comp α.ringMap.toRingHom = β.ringMap.toRingHom)

include hφ in
theorem overBase : φ.comp U.base = T.base := by
  rw [← α.overBase, ← RingHom.comp_assoc, hφ, β.overBase]

include hgen hφ in
theorem isDPMorphism : DividedPowers.IsDPMorphism U.dividedPowers T.dividedPowers φ := by
  apply DividedPowers.IsDPMorphism.of_comp δ U.dividedPowers T.dividedPowers
    U.base φ hgen U.baseCompatible
  rw [BaseGeneratedFrameLift.overBase α β φ hφ]
  exact T.baseCompatible

def dp : DividedPowers.DPMorphism U.dividedPowers T.dividedPowers where
  toRingHom := φ
  ideal_comp := (isDPMorphism α β hgen φ hφ).ideal_comp
  dpow_comp := (isDPMorphism α β hgen φ hφ).dpow_comp

theorem dp_comp : (dp α β hgen φ hφ).comp α.ringMap = β.ringMap := by
  ext x
  exact RingHom.congr_fun hφ x

theorem closed_comp :
    Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap T U (dp α β hgen φ hφ))) ≫
      IntegralComparison.BigCrystallineSite.Object.closed.map α = IntegralComparison.BigCrystallineSite.Object.closed.map β := by
  change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap T U (dp α β hgen φ hφ))) ≫
    Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U V α.ringMap)) = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((IntegralComparison.BigCrystallineSite.Object.quotientMap T U (dp α β hgen φ hφ)).comp (IntegralComparison.BigCrystallineSite.Object.quotientMap U V α.ringMap))) = _
  rw [← IntegralComparison.BigCrystallineSite.Object.quotientMap_comp, dp_comp]
  rfl

def lift : T ⟶ U where
  ringMap := dp α β hgen φ hφ
  overBase := BaseGeneratedFrameLift.overBase α β φ hφ
  overX := by
    rw [← α.overX, ← Category.assoc]
    change (Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap T U (dp α β hgen φ hφ))) ≫
      IntegralComparison.BigCrystallineSite.Object.closed.map α) ≫ V.mapToX = T.mapToX
    rw [closed_comp]
    exact β.overX

theorem lift_comp : lift α β hgen φ hφ ≫ α = β := by
  apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
  exact dp_comp α β hgen φ hφ

theorem lift_ringMap : (lift α β hgen φ hφ).ringMap.toRingHom = φ := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BaseGenerated.BaseGeneratedFrameLift
