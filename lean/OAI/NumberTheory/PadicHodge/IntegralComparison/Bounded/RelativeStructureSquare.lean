import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafRestriction

/-! # Relative Structure Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureSquare

noncomputable section

/-!
# IntegralComparison: the actual relative-resolution structure isomorphism commutes with geometric restriction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "restriction" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def transported : (RelativeSheafComplex.sheafification f n).obj
    (RelativeCrystalline.ModuleComplex.ambientPresheaf QX) ⟶
      BoundedCrystalline.CrystallineCohomology.structureSheaf f n :=
  ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
    (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)).hom.app ((QY).op ⋙ BigCrystallineCohomology.largePresheaf fY) ≫
      (restriction).map (RelativeSheafComplex.structureIso fY n).hom ≫
        (BoundedOpen.Sheaves.structureTransport g hg n).hom

theorem transported_app (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) :
    (transported g hg n).hom.app U =
      (((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
        (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)).hom.app
          ((QY).op ⋙ BigCrystallineCohomology.largePresheaf fY)).hom.app U ≫
        (RelativeSheafComplex.structureIso fY n).hom.hom.app (op ((G).obj U.unop)) ≫
          (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom.app U := rfl

theorem unit_coordinates : toSheafify (BoundedCrystalline.Site.topology f n) ((QX).op ⋙ BigCrystallineCohomology.largePresheaf f) ≫
    (transported g hg n).hom = (StructureCoordinates.presheafIso f n).hom := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let β := (BoundedOpen.Sheaves.structureTransport g hg n).hom.hom.app U
  let γ := (RelativeSheafComplex.structureIso fY n).hom.hom.app (op ((G).obj U.unop))
  have h₁ := congrArg (fun η => β (γ (η.app U x)))
    ((G).toSheafify_pullbackSheafificationCompatibility (ModuleCat.{u + 1} R)
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) ((QY).op ⋙ BigCrystallineCohomology.largePresheaf fY))
  have h₂ := congrArg (fun η => β (η.app (op ((G).obj U.unop)) x))
    (RelativeStructureUnit.unit (p := p) (J := J) (δ := δ) fY n)
  have h₃ := congrArg (fun η => η.app U x) (StructureCoordinates.coordinates n g hg)
  have h₀ := congrArg (fun η => η ((toSheafify (BoundedCrystalline.Site.topology f n)
    ((QX).op ⋙ BigCrystallineCohomology.largePresheaf f)).app U x)) (transported_app g hg n U)
  exact h₀.trans (h₁.trans (h₂.trans h₃))

theorem square : transported (p := p) (J := J) (δ := δ) g hg n =
    (RelativeSheafComplex.structureIso (p := p) (J := J) (δ := δ) f n).hom := by
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext (BoundedCrystalline.Site.topology f n) _ _
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n).property
  exact (unit_coordinates g hg n).trans (RelativeStructureUnit.unit f n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureSquare
