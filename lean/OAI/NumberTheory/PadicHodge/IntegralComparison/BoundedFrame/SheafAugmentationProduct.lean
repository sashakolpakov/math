import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafCechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.CechProduct

/-! # Sheaf Augmentation Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct

noncomputable section

/-! The literal ambient-ring coefficient augmentation into the bounded
relative PD sheaf complex preserves the native Čech cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p) (J := J) (δ := δ) (f := f) (n := n)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct.coefficientComplex f n F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product.underlyingComplex f n F
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves (p := p) (J := J) (δ := δ) f n

def ambient : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u + 1} R :=
  (BoundedCrystalline.Site.inclusion f n).op ⋙ BigCrystallineCohomology.largePresheaf f

def coefficientAugmentation : ambient f n ⟶ (L).X 0 :=
  (S).map (RelativeCrystalline.ModuleComplex.augmentationZero H Q π)

theorem coefficientAugmentation_closed : coefficientAugmentation f n F ≫ (L).d 0 1 = 0 := by
  exact ((S).map_comp (RelativeCrystalline.ModuleComplex.augmentationZero H Q π)
    ((Diagram.complex F).d 0 1)).symm.trans
    ((congrArg (fun a : RelativeCrystalline.ModuleComplex.ambientPresheaf Q ⟶
        (Diagram.complex F).X 1 => (S).map a)
      (RelativeCrystalline.CechProduct.augmentation_closed H Q π)).trans ((S).map_zero _ _))

def ambientPairing (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) :
    (ambient f n).obj U →ₗ[R] (ambient f n).obj U →ₗ[R] (ambient f n).obj U :=
  Crystalline.CoefficientPairing.lift B _ _ _ (RelativeCrystalline.CechProduct.coefficientPairing Q U)

omit [Fact (Nat.Prime p)] [IsSeparated f] in
theorem ambientPairing_natural {U V : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ}
    (α : U ⟶ V) (x y : (ambient f n).obj U) :
    (ambient f n).map α (ambientPairing f n U x y) =
      ambientPairing f n V ((ambient f n).map α x) ((ambient f n).map α y) := by
  apply ULift.ext
  exact RelativeCrystalline.CechProduct.coefficientPairing_natural Q α x.down y.down

theorem coefficientAugmentation_mul (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x y : (ambient f n).obj U) :
    (coefficientAugmentation f n F).app U (ambientPairing f n U x y) =
      SheafProduct.coefficientPairing f n F 0 0 U
        ((coefficientAugmentation f n F).app U x) ((coefficientAugmentation f n F).app U y) := by
  apply ULift.ext
  exact RelativeCrystalline.Product.augmentationZero_mul H Q π U x.down y.down

def augmentation : ambient f n ⟶ (K).X 0 := coefficientAugmentation f n F ≫ SheafProduct.unitMap f n F 0

theorem augmentation_closed : augmentation f n F ≫ (K).d 0 1 = 0 := by
  change (coefficientAugmentation f n F ≫ (SheafCechProduct.sheafificationMap f n F).f 0) ≫
    (K).d 0 1 = 0
  rw [Category.assoc, (SheafCechProduct.sheafificationMap f n F).comm 0 1,
    ← Category.assoc, coefficientAugmentation_closed, zero_comp]

theorem augmentation_mul (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x y : (ambient f n).obj U) :
    (augmentation f n F).app U (ambientPairing f n U x y) =
      SheafProduct.sectionPairing f n F 0 0 U ((augmentation f n F).app U x) ((augmentation f n F).app U y) :=
  (congrArg ((SheafProduct.unitMap f n F 0).app U) (coefficientAugmentation_mul f n F U x y)).trans
    (SheafProduct.unitMap_pairing f n F 0 0 U
      ((coefficientAugmentation f n F).app U x) ((coefficientAugmentation f n F).app U y))

variable (N : SimplicialObject (FormalCoproduct.{u} (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)))

def sourceCup := Presheaf.AugmentationCohomology.Product.sourceCohomologyCup.{u + 1, u, u, u + 1, u + 1}
  N (ambient f n) (ambientPairing f n) (ambientPairing_natural f n)

def totalMap := Presheaf.AugmentationProduct.map.{u + 1, u, u, u + 1, u + 1}
  N K (ambient f n) (augmentation f n F) (augmentation_closed f n F)

abbrev totalMap_cup := Presheaf.AugmentationCohomology.Product.cohomologyMap_cup.{u + 1, u, u, u + 1, u + 1}
  N (ambient f n) (ambientPairing f n) (ambientPairing_natural f n)
  K (augmentation f n F) (augmentation_closed f n F) (SheafProduct.sectionPairing f n F)
  (SheafProduct.sectionPairing_natural f n F) (SheafLeibniz.Product.sectionPairing_differential f n F) (augmentation_mul f n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct
