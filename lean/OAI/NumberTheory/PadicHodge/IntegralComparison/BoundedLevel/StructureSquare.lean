import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheaves

/-! # Structure Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureSquare

noncomputable section

/-!
# IntegralComparison: the actual relative-resolution structure isomorphism commutes with restriction between Witt levels
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "restriction" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def transported : (Bounded.RelativeSheafComplex.sheafification f n).obj
    (RelativeCrystalline.ModuleComplex.ambientPresheaf QX) ⟶
      BoundedCrystalline.CrystallineCohomology.structureSheaf f n :=
  ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
    (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).hom.app ((QY).op ⋙ BigCrystallineCohomology.largePresheaf f) ≫
      (restriction).map (Bounded.RelativeSheafComplex.structureIso f m).hom ≫
        (Bounded.CohomologyTransition.structureIso f n m hnm).hom

theorem transported_app (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) :
    (transported f n m hnm).hom.app U =
      (((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R)
        (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).hom.app
          ((QY).op ⋙ BigCrystallineCohomology.largePresheaf f)).hom.app U ≫
        (Bounded.RelativeSheafComplex.structureIso f m).hom.hom.app (op ((G).obj U.unop)) ≫
          (Bounded.CohomologyTransition.structureIso f n m hnm).hom.hom.app U := rfl

theorem unit_coordinates : toSheafify (BoundedCrystalline.Site.topology f n) ((QX).op ⋙ BigCrystallineCohomology.largePresheaf f) ≫
    (transported f n m hnm).hom = (Bounded.StructureCoordinates.presheafIso f n).hom := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let β := (Bounded.CohomologyTransition.structureIso f n m hnm).hom.hom.app U
  let γ := (Bounded.RelativeSheafComplex.structureIso f m).hom.hom.app (op ((G).obj U.unop))
  have h₁ := congrArg (fun η => β (γ (η.app U x)))
    ((G).toSheafify_pullbackSheafificationCompatibility (ModuleCat.{u + 1} R)
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m) ((QY).op ⋙ BigCrystallineCohomology.largePresheaf f))
  have h₂ := congrArg (fun η => β (η.app (op ((G).obj U.unop)) x))
    (Bounded.RelativeStructureUnit.unit (p := p) (J := J) (δ := δ) f m)
  have h₃ := congrArg (fun η => η.app U x) (StructureCoordinates.coordinates f n m hnm)
  have h₀ := congrArg (fun η => η ((toSheafify (BoundedCrystalline.Site.topology f n)
    ((QX).op ⋙ BigCrystallineCohomology.largePresheaf f)).app U x)) (transported_app f n m hnm U)
  exact h₀.trans (h₁.trans (h₂.trans h₃))

theorem square : transported (p := p) (J := J) (δ := δ) f n m hnm =
    (Bounded.RelativeSheafComplex.structureIso (p := p) (J := J) (δ := δ) f n).hom := by
  apply Sheaf.hom_ext
  apply CategoryTheory.sheafify_hom_ext (BoundedCrystalline.Site.topology f n) _ _
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n).property
  exact (unit_coordinates f n m hnm).trans (Bounded.RelativeStructureUnit.unit f n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureSquare
