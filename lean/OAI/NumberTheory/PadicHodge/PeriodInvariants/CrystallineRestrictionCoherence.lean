import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SheafificationCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

/-! # Crystalline Restriction Coherence -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence

noncomputable section

/-!
# Coherent restriction on the actual big crystalline sites

Postcomposition preserves the ambient rings. The canonical identity and
composition isomorphisms therefore act as identity maps on these rings.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y Z : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}

def postcomposeIdComponent (U : IntegralComparison.BigCrystallineSite.Object p B J δ f) :
    (IntegralComparison.BigCrystallineSite.postcompose (𝟙 X) (Category.id_comp f)).obj U ≅ U where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ U.mapToX = U.mapToX ≫ 𝟙 X
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ U.mapToX = U.mapToX ≫ 𝟙 X
        rw [Spec.map_id, Category.id_comp, Category.comp_id] }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ (U.mapToX ≫ 𝟙 X) = U.mapToX
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ (U.mapToX ≫ 𝟙 X) = U.mapToX
        rw [Spec.map_id, Category.id_comp, Category.comp_id] }
  hom_inv_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl

def postcomposeId : IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) (𝟙 X) (Category.id_comp f) ≅ 𝟭 _ :=
  NatIso.ofComponents postcomposeIdComponent (by
    intro U V α
    apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
    rfl)

variable (g : X ⟶ Y) (hg : g ≫ fY = f) (h : Y ⟶ Z) (hh : h ≫ fZ = fY)

include hg hh in
theorem composite_over : (g ≫ h) ≫ fZ = f := by rw [Category.assoc, hh, hg]

def postcomposeCompComponent (U : IntegralComparison.BigCrystallineSite.Object p B J δ f) :
    (IntegralComparison.BigCrystallineSite.postcompose h hh).obj ((IntegralComparison.BigCrystallineSite.postcompose g hg).obj U) ≅
      (IntegralComparison.BigCrystallineSite.postcompose (g ≫ h) (composite_over g hg h hh)).obj U where
  hom :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ (U.mapToX ≫ (g ≫ h)) = (U.mapToX ≫ g) ≫ h
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ _ = _
        rw [Spec.map_id, Category.id_comp, Category.assoc] }
  inv :=
    { ringMap := DividedPowers.DPMorphism.id U.dividedPowers
      overBase := rfl
      overX := by
        change Spec.map (CommRingCat.ofHom (IntegralComparison.BigCrystallineSite.Object.quotientMap U U
          (DividedPowers.DPMorphism.id U.dividedPowers))) ≫ ((U.mapToX ≫ g) ≫ h) = U.mapToX ≫ (g ≫ h)
        rw [IntegralComparison.BigCrystallineSite.Object.quotientMap_id]
        change Spec.map (𝟙 (CommRingCat.of (U.ring ⧸ U.ideal))) ≫ _ = _
        rw [Spec.map_id, Category.id_comp, Category.assoc] }
  hom_inv_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl
  inv_hom_id := by apply IntegralComparison.BigCrystallineSite.Object.Hom.ext; rfl

def postcomposeComp :
    IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg ⋙ IntegralComparison.BigCrystallineSite.postcompose h hh ≅
      IntegralComparison.BigCrystallineSite.postcompose (g ≫ h) (composite_over g hg h hh) :=
  NatIso.ofComponents (postcomposeCompComponent g hg h hh) (by
    intro U V α
    apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
    rfl)

omit g hg h hh in
def restrictionId : IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) (𝟙 X) (Category.id_comp f) ≅
    𝟭 (IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f) :=
  Functor.sheafPushforwardContinuousId' postcomposeId (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)))
    IntegralComparison.BigCrystallineSite.Object.topology

def restrictionComp : IntegralComparison.Crystalline.ExactRestriction.restriction (p := p) (J := J) (δ := δ) h hh ⋙ IntegralComparison.Crystalline.ExactRestriction.restriction g hg ≅
    IntegralComparison.Crystalline.ExactRestriction.restriction (g ≫ h) (composite_over g hg h hh) := by
  letI := Functor.isContinuous_comp (IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg)
    (IntegralComparison.BigCrystallineSite.postcompose h hh)
    IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology
  exact Functor.sheafPushforwardContinuousIso (postcomposeComp (p := p) (J := J) (δ := δ) g hg h hh)
    (ModuleCat.{u + 1} (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))) IntegralComparison.BigCrystallineSite.Object.topology IntegralComparison.BigCrystallineSite.Object.topology

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineRestrictionCoherence
