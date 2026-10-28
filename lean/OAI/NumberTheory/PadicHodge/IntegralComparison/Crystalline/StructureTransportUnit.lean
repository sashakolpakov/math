import OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationTransportUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Structure Transport Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureTransportUnit

noncomputable section

/-!
# IntegralComparison: geometric crystalline pullback preserves the canonical ambient-ring section maps
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f)

theorem unit : Functor.whiskerLeft (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).op
      (toSheafify BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf fY)) ≫ (BigCrystallineCohomology.structureTransport g hg).hom.hom =
    (BigCrystallineCohomology.presheafTransport g hg).hom ≫ toSheafify BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f) :=
  SheafificationTransportUnit.unit (BigCrystallineSite.postcompose g hg) (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf fY) (BigCrystallineCohomology.largePresheaf f) (BigCrystallineCohomology.presheafTransport g hg)

theorem coordinates : Functor.whiskerLeft (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).op
      (StructureDescent.structurePresheafIso fY).hom ≫ (BigCrystallineCohomology.structureTransport g hg).hom.hom =
    (BigCrystallineCohomology.presheafTransport g hg).hom ≫ (StructureDescent.structurePresheafIso f).hom := by
  exact unit g hg

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureTransportUnit
