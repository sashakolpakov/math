import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition

/-! # Pulled Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PulledAugmentation

noncomputable section

/-!
# IntegralComparison: pulling back the original bounded frame augmentation through restriction between Witt levels
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  [Fact p.Prime] [IsSeparated f]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((CochainComplex.single₀ _).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf f m)) ≅
      (CochainComplex.single₀ _).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf f n) :=
  Single.ComplexTransport.sourceIso R (Bounded.CohomologyTransition.structureIso f n m hnm)

def augmentation : (CochainComplex.single₀ _).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n) ⟶
      ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Bounded.RelativeSheafComplex.complex f m F) :=
  Single.ComplexTransport.map R (Bounded.CohomologyTransition.structureIso f n m hnm)
    (Bounded.RelativeSheafComplex.augmentation f m F)

theorem zero : (augmentation f n m hnm F).f 0 = (Bounded.CohomologyTransition.structureIso f n m hnm).inv ≫
    (R).map ((Bounded.RelativeSheafComplex.augmentation f m F).f 0) :=
  Single.ComplexTransport.map_zero R (Bounded.CohomologyTransition.structureIso f n m hnm)
    (Bounded.RelativeSheafComplex.augmentation f m F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PulledAugmentation
