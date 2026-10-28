import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureTransportUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves

/-! # Structure Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates

noncomputable section

/-!
# IntegralComparison: original bounded crystalline structure sheaves retain their ambient-ring coordinates under pullback
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def presheafIso : (BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙ BigCrystallineCohomology.largePresheaf f ≅
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n).obj :=
  Functor.isoWhiskerLeft (BoundedCrystalline.Site.inclusion f n).op (Crystalline.StructureDescent.structurePresheafIso f)

variable {f} {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)} (g : X ⟶ Y) (hg : g ≫ fY = f)

def presheafTransport :
    (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).op ⋙
      ((BoundedCrystalline.Site.inclusion fY n).op ⋙ BigCrystallineCohomology.largePresheaf fY) ≅
        (BoundedCrystalline.Site.inclusion f n).op ⋙ BigCrystallineCohomology.largePresheaf f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

theorem coordinates : Functor.whiskerLeft
    (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).op (presheafIso fY n).hom ≫
      (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom =
    (presheafTransport n g hg).hom ≫ (presheafIso f n).hom := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun β => β.app (op U.unop.obj) x) (Crystalline.StructureTransportUnit.coordinates g hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates
