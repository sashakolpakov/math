import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CartesianMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Inverse

/-! # Isomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Isomorphism

noncomputable section

/-!
# IntegralComparison: recognizing isomorphisms of crystalline thickenings

The inverse is constructed as a divided-power ring map and checked over
the base and over X. The quotient-ring condition preserves the ideal.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U V : BigCrystallineSite.Object p B J δ f} (α : U ⟶ V)
variable (hα : Function.Bijective α.ringMap)
variable (hq : Function.Injective (BigCrystallineSite.Object.quotientMap U V α.ringMap))

def inverseDP : DividedPowers.DPMorphism U.dividedPowers V.dividedPowers :=
  DividedPower.Inverse.inverse α.ringMap hα hq

lemma inverseDP_comp : (inverseDP α hα hq).comp α.ringMap =
    DividedPowers.DPMorphism.id V.dividedPowers :=
  DividedPower.Inverse.inverse_comp α.ringMap hα hq

lemma comp_inverseDP : α.ringMap.comp (inverseDP α hα hq) =
    DividedPowers.DPMorphism.id U.dividedPowers :=
  DividedPower.Inverse.comp_inverse α.ringMap hα hq

private lemma inverse_quotient_comp :
    (BigCrystallineSite.Object.quotientMap V U (inverseDP α hα hq)).comp (BigCrystallineSite.Object.quotientMap U V α.ringMap) =
      RingHom.id (V.ring ⧸ V.ideal) := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, inverseDP_comp, BigCrystallineSite.Object.quotientMap_id]

def inverseHom : V ⟶ U where
  ringMap := inverseDP α hα hq
  overBase := by
    apply RingHom.ext
    intro b
    apply hα.injective
    have he := DFunLike.congr_fun (comp_inverseDP α hα hq) (U.base b)
    change α.ringMap ((inverseDP α hα hq) (U.base b)) = U.base b at he
    exact he.trans (DFunLike.congr_fun α.overBase b).symm
  overX := by
    rw [← α.overX, ← Category.assoc, ← Spec.map_comp]
    have he := congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (inverse_quotient_comp α hα hq)
    change Spec.map (CommRingCat.ofHom
      ((BigCrystallineSite.Object.quotientMap V U (inverseDP α hα hq)).comp (BigCrystallineSite.Object.quotientMap U V α.ringMap))) ≫
        V.mapToX = V.mapToX
    rw [he]
    simp

def iso : U ≅ V where
  hom := α
  inv := inverseHom α hα hq
  hom_inv_id := by
    apply BigCrystallineSite.Object.Hom.ext
    exact comp_inverseDP α hα hq
  inv_hom_id := by
    apply BigCrystallineSite.Object.Hom.ext
    exact inverseDP_comp α hα hq

include hα hq in
lemma isIso_of_ring_bijective_quotient_injective : IsIso α :=
  (iso α hα hq).isIso_hom

omit hα hq in
lemma isIso_of_cartesian [IsIso (BigCrystallineSite.Object.ambient.map α)] (h : BigCrystallineSite.Object.Cartesian α) : IsIso α := by
  have hclosed : IsIso (BigCrystallineSite.Object.closed.map α) := h.isIso_fst_of_isIso
  have : IsIso (Scheme.Spec.map (CommRingCat.ofHom α.ringMap.toRingHom).op) :=
    inferInstanceAs (IsIso (BigCrystallineSite.Object.ambient.map α))
  have hringop : IsIso (CommRingCat.ofHom α.ringMap.toRingHom).op :=
    isIso_of_reflects_iso _ Scheme.Spec
  have hring : IsIso (CommRingCat.ofHom α.ringMap.toRingHom) := isIso_of_op _
  have : IsIso (Scheme.Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)).op) := hclosed
  have hquotop : IsIso (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)).op :=
    isIso_of_reflects_iso _ Scheme.Spec
  have hquot : IsIso (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap)) := isIso_of_op _
  exact isIso_of_ring_bijective_quotient_injective α
    (ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom α.ringMap.toRingHom))
    (ConcreteCategory.bijective_of_isIso
      (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U V α.ringMap))).injective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Isomorphism
