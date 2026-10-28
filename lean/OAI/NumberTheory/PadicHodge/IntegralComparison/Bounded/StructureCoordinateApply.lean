import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates

/-! # Structure Coordinate Apply -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinateApply

noncomputable section

/-! Elementwise form of the original crystalline structure-coordinate compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

theorem apply (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)ᵒᵖ)
    (x : (BigCrystallineCohomology.largePresheaf fX).obj (op U.unop.obj)) :
    (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom.app U
      ((StructureCoordinates.presheafIso fY n).hom.app (op ((G).obj U.unop)) x) =
        (StructureCoordinates.presheafIso fX n).hom.app U x :=
  congrArg (fun a => a.app U x) (StructureCoordinates.coordinates n g hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinateApply
