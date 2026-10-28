import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Continuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Open Condition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenCondition

noncomputable section

/-!
# IntegralComparison: original crystalline objects whose closed map factors through a geometric chart
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y)

def property : ObjectProperty (BigCrystallineSite.Object p B J δ fY) := fun U =>
  ∃ t : Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ X, t ≫ g = U.mapToX

theorem incoming {U V : BigCrystallineSite.Object p B J δ fY} (α : U ⟶ V) (hV : property g V) : property g U := by
  obtain ⟨t, ht⟩ := hV
  exact ⟨BigCrystallineSite.Object.closed.map α ≫ t, (Category.assoc _ _ _).trans
    ((congrArg (fun s => BigCrystallineSite.Object.closed.map α ≫ s) ht).trans α.overX)⟩

variable (hg : g ≫ fY = f)
  (U : BigCrystallineSite.Object p B J δ fY) (t : Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ X)
  (ht : t ≫ g = U.mapToX)

def liftObject : BigCrystallineSite.Object p B J δ f where
  ring := U.ring
  base := U.base
  ideal := U.ideal
  dividedPowers := U.dividedPowers
  baseCompatible := U.baseCompatible
  primeNilpotent := U.primeNilpotent
  nilIdeal := U.nilIdeal
  mapToX := t
  overBase := by
    rw [← hg, ← Category.assoc, ht, U.overBase]

theorem liftObject_property (n : ℕ) (hU : BoundedCrystalline.Site.property fY n U) :
    BoundedCrystalline.Site.property f n (liftObject g hg U t ht) := hU

def liftIso : (BigCrystallineSite.postcompose g hg).obj (liftObject g hg U t ht) ≅ U where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ U.mapToX = t ≫ g
        rw [BigCrystallineSite.Object.quotientMap_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact ht.symm }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ (t ≫ g) = U.mapToX
        rw [BigCrystallineSite.Object.quotientMap_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact ht }
  hom_inv_id := by apply BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply BigCrystallineSite.Object.Hom.ext; rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenCondition
