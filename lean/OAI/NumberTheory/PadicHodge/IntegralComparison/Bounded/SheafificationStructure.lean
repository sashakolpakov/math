import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureSquare

/-! # Sheafification Structure -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafificationStructure

noncomputable section

/-!
# IntegralComparison: the frame sheafification comparison preserves the original structure isomorphism
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.ambientPresheaf QY
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

theorem comparison_inv : (BoundedFrame.SheafRestriction.sheafificationIso g hg n).inv.app A =
    ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)).hom.app
        ((QY).op ⋙ BigCrystallineCohomology.largePresheaf fY) := rfl

theorem square : (BoundedFrame.SheafRestriction.sheafificationIso g hg n).inv.app A ≫
    (R).map (RelativeSheafComplex.structureIso fY n).hom ≫
      (BoundedOpen.Sheaves.structureTransport g hg n).hom =
        (RelativeSheafComplex.structureIso (p := p) (J := J) (δ := δ) f n).hom := by
  exact (congrArg (fun a => a ≫ (R).map (RelativeSheafComplex.structureIso fY n).hom ≫
    (BoundedOpen.Sheaves.structureTransport g hg n).hom) (comparison_inv g hg n)).trans
      (RelativeStructureSquare.square g hg n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafificationStructure
