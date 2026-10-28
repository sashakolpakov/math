import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Geometric Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap

noncomputable section

/-!
# IntegralComparison: a map of frames over a geometric chart induces an augmented sheaf-complex map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

variable (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

def map : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Bounded.RelativeSheafComplex.complex fY n FY) ⟶
      Bounded.RelativeSheafComplex.complex f n FX :=
  ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map (Change.sheafMap α) ≫
    (SheafRestriction.complexIso g hg n FX).hom

theorem augmentation : PullbackAugmentation.augmentation g hg n FY ≫ GeometricMap.map g hg n α =
    Bounded.RelativeSheafComplex.augmentation f n FX := by
  have h := (Single.ComplexTransportNaturality.comp R (BoundedOpen.Sheaves.structureTransport g hg n)
    (Bounded.RelativeSheafComplex.augmentation fY n FY) (Change.sheafMap α)).trans
      (congrArg (Single.ComplexTransport.map R (BoundedOpen.Sheaves.structureTransport g hg n))
        (Change.sheaf_augmentation α))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (SheafRestriction.complexIso g hg n FX).hom) h).trans
      (SheafAugmentation.augmentation g hg n FX))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap
