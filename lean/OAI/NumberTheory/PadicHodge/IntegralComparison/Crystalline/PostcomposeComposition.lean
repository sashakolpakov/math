import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Postcompose Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition

noncomputable section

/-! Composition of the actual crystalline geometric functors retains identity maps on PD rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY)

include hg hh in
theorem overBase : (g ≫ h) ≫ fZ = fX :=
  (Category.assoc _ _ _).trans ((congrArg (fun a => g ≫ a) hh).trans hg)

def objectIso (U : BigCrystallineSite.Object p B J δ fX) :
    (BigCrystallineSite.postcompose h hh).obj ((BigCrystallineSite.postcompose g hg).obj U) ≅
      (BigCrystallineSite.postcompose (g ≫ h) (PostcomposeComposition.overBase g h hg hh)).obj U where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ (U.mapToX ≫ (g ≫ h)) = (U.mapToX ≫ g) ≫ h
        rw [BigCrystallineSite.Object.quotientMap_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact (Category.assoc _ _ _).symm }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ ((U.mapToX ≫ g) ≫ h) = U.mapToX ≫ (g ≫ h)
        rw [BigCrystallineSite.Object.quotientMap_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
        exact Category.assoc _ _ _ }
  hom_inv_id := by apply BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply BigCrystallineSite.Object.Hom.ext; rfl

def iso : BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg ⋙ BigCrystallineSite.postcompose h hh ≅
    BigCrystallineSite.postcompose (g ≫ h) (PostcomposeComposition.overBase g h hg hh) :=
  NatIso.ofComponents (objectIso g h hg hh) (by intro U V α; apply BigCrystallineSite.Object.Hom.ext; rfl)

def boundedIso (n : ℕ) :
    BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n ⋙
      BoundedOpen.Equivalence.postcompose h hh n ≅
    BoundedOpen.Equivalence.postcompose (g ≫ h) (PostcomposeComposition.overBase g h hg hh) n :=
  NatIso.ofComponents
    (fun U => (BoundedCrystalline.Site.property fZ n).isoMk (objectIso g h hg hh U.obj))
    (by
      intro U V α
      apply (BoundedCrystalline.Site.inclusion fZ n).map_injective
      apply BigCrystallineSite.Object.Hom.ext
      rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition
