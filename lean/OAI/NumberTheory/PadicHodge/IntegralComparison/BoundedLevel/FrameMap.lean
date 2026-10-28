import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Frame Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap

noncomputable section

/-!
# IntegralComparison: a map of frames over a bounded level induces an augmented sheaf-complex map
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  [Fact p.Prime] [IsSeparated f]
  {FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m}

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

variable (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj FX ⟶ FY)

def map : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (Bounded.RelativeSheafComplex.complex f m FY) ⟶
      Bounded.RelativeSheafComplex.complex f n FX :=
  ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map (BoundedFrame.Change.sheafMap α) ≫
    (FrameSheaves.complexIso f n m hnm FX).hom

theorem augmentation : PulledAugmentation.augmentation f n m hnm FY ≫ FrameMap.map f n m hnm α =
    Bounded.RelativeSheafComplex.augmentation f n FX := by
  have h := (Single.ComplexTransportNaturality.comp R (Bounded.CohomologyTransition.structureIso f n m hnm)
    (Bounded.RelativeSheafComplex.augmentation f m FY) (BoundedFrame.Change.sheafMap α)).trans
      (congrArg (Single.ComplexTransport.map R (Bounded.CohomologyTransition.structureIso f n m hnm))
        (BoundedFrame.Change.sheaf_augmentation α))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (FrameSheaves.complexIso f n m hnm FX).hom) h).trans
      (FrameSheafAugmentation.augmentation f n m hnm FX))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap
