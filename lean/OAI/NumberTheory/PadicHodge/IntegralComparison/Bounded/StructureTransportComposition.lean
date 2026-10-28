import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RestrictionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinateApply

/-! # Structure Transport Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureTransportComposition

noncomputable section

/-! Nested crystalline structure-sheaf transport agrees with transport along the composite chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (n : ℕ)

local notation "Fg" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "Fh" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) h hh n
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition.overBase g h hg hh
local notation "Fc" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) (g ≫ h) hc n
local notation "OZ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fZ n
local notation "Rg" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

theorem coordinates (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)ᵒᵖ)
    (x : (BigCrystallineCohomology.largePresheaf fX).obj (op U.unop.obj)) :
    (RestrictionComposition.objectIso g h hg hh n OZ).hom.hom.app U
      ((StructureCoordinates.presheafIso fZ n).hom.app (op ((Fh).obj ((Fg).obj U.unop))) x) =
    (StructureCoordinates.presheafIso fZ n).hom.app (op ((Fc).obj U.unop)) x := by
  let α := ((Crystalline.PostcomposeComposition.boundedIso g h hg hh n).inv.app U.unop).op
  have hnat := congrArg (fun a => a x)
    ((StructureCoordinates.presheafIso fZ n).hom.naturality α)
  exact (congrArg (fun a => a ((StructureCoordinates.presheafIso fZ n).hom.app
    (op ((Fh).obj ((Fg).obj U.unop))) x))
      (RestrictionComposition.component g h hg hh n OZ U)).trans hnat.symm

theorem hom : (Rg).map (BoundedOpen.Sheaves.structureTransport h hh n).hom ≫
    (BoundedOpen.Sheaves.structureTransport g hg n).hom =
      (RestrictionComposition.objectIso g h hg hh n OZ).hom ≫
        (BoundedOpen.Sheaves.structureTransport (g ≫ h) hc n).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := ((StructureCoordinates.presheafIso fZ n).app
    (op ((Fh).obj ((Fg).obj U.unop)))).toLinearEquiv.surjective y
  change (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom.app U
      ((BoundedOpen.Sheaves.structureTransport h hh n).hom.hom.app (op ((Fg).obj U.unop))
        ((StructureCoordinates.presheafIso fZ n).hom.app (op ((Fh).obj ((Fg).obj U.unop))) x)) =
    (BoundedOpen.Sheaves.structureTransport (g ≫ h) hc n).hom.hom.app U
      ((RestrictionComposition.objectIso g h hg hh n OZ).hom.hom.app U
        ((StructureCoordinates.presheafIso fZ n).hom.app (op ((Fh).obj ((Fg).obj U.unop))) x))
  have hleft := (congrArg (fun a => (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom.app U a)
    (StructureCoordinateApply.apply h hh n (op ((Fg).obj U.unop)) x)).trans
      (StructureCoordinateApply.apply g hg n U x)
  have hright := (congrArg (fun a => (BoundedOpen.Sheaves.structureTransport (g ≫ h) hc n).hom.hom.app U a)
    (coordinates g h hg hh n U x)).trans
      (StructureCoordinateApply.apply (g ≫ h) hc n U x)
  exact hleft.trans hright.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureTransportComposition
