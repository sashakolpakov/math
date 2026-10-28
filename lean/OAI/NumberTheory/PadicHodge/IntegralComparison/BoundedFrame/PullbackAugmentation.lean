import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves

/-! # Pullback Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PullbackAugmentation

noncomputable section

/-!
# IntegralComparison: pulling back the original bounded frame augmentation through geometric restriction
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ) [IsSeparated fY]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((CochainComplex.single₀ _).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf fY n)) ≅
      (CochainComplex.single₀ _).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) :=
  Single.ComplexTransport.sourceIso R (BoundedOpen.Sheaves.structureTransport g hg n)

def augmentation : (CochainComplex.single₀ _).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) ⟶
      ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Bounded.RelativeSheafComplex.complex fY n F) :=
  Single.ComplexTransport.map R (BoundedOpen.Sheaves.structureTransport g hg n)
    (Bounded.RelativeSheafComplex.augmentation fY n F)

theorem zero : (augmentation g hg n F).f 0 = (BoundedOpen.Sheaves.structureTransport g hg n).inv ≫
    (R).map ((Bounded.RelativeSheafComplex.augmentation fY n F).f 0) :=
  Single.ComplexTransport.map_zero R (BoundedOpen.Sheaves.structureTransport g hg n)
    (Bounded.RelativeSheafComplex.augmentation fY n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PullbackAugmentation
