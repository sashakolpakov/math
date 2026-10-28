import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.AugmentationTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.SheafificationStructure
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PulledAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameAugmentation

/-! # Frame Sheaf Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafAugmentation

noncomputable section

/-!
# IntegralComparison: restriction between Witt levels preserves the original bounded frame sheaf augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  [Fact p.Prime] [IsSeparated f]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f m
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

theorem comparison_f (i : ℕ) : (FrameSheaves.complexIso f n m hnm F).hom.f i =
    (FrameSheaves.sheafificationIso f n m hnm).hom.app
      ((BoundedFrame.Diagram.complex ((G).obj F)).X i) ≫
        (SX).map ((FrameRestriction.presheafIso f n m hnm F).hom.f i) := rfl

theorem zero : (PulledAugmentation.augmentation f n m hnm ((G).obj F)).f 0 ≫
    (FrameSheaves.complexIso f n m hnm F).hom.f 0 =
      (Bounded.RelativeSheafComplex.augmentation f n F).f 0 := by
  have h := Sheaf.AugmentationTransport.augmentation
    (Relative.ComplexRestriction.restriction (B := B) G) SY SX R
    (FrameSheaves.sheafificationIso f n m hnm)
    (Bounded.RelativeSheafComplex.structureIso f m)
    (Bounded.CohomologyTransition.structureIso f n m hnm)
    (Bounded.RelativeSheafComplex.structureIso f n)
    (SheafificationStructure.square f n m hnm)
    (RelativeCrystalline.ModuleComplex.augmentationZero
      (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
      (BoundedFrame.Diagram.projection ((G).obj F)))
    ((FrameRestriction.presheafIso f n m hnm F).hom.f 0)
    (RelativeCrystalline.ModuleComplex.augmentationZero
      (BoundedFrame.Diagram.productDiagram F) QX (BoundedFrame.Diagram.projection F))
    (FrameAugmentation.zero f n m hnm F)
  have h₀ := PulledAugmentation.zero f n m hnm ((G).obj F)
  have h₁ := Bounded.SheafAugmentationZero.zero f m ((G).obj F)
  have h₂ := comparison_f f n m hnm F 0
  have h₃ := Bounded.SheafAugmentationZero.zero f n F
  exact (congrArg₂ (fun a b => a ≫ b)
    (h₀.trans (congrArg (fun a => (Bounded.CohomologyTransition.structureIso f n m hnm).inv ≫ (R).map a) h₁))
      h₂).trans ((Category.assoc _ _ _).trans (h.trans h₃.symm))

theorem augmentation : PulledAugmentation.augmentation f n m hnm ((G).obj F) ≫
    (FrameSheaves.complexIso f n m hnm F).hom =
      Bounded.RelativeSheafComplex.augmentation f n F := by
  apply (CochainComplex.fromSingle₀Equiv (Bounded.RelativeSheafComplex.complex f n F)
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)).injective
  apply Subtype.ext
  exact zero f n m hnm F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSheafAugmentation
