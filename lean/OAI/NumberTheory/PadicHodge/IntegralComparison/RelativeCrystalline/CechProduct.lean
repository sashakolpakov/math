import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationCohomology
import Mathlib.Algebra.Algebra.Bilinear

/-! # Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.CechProduct

noncomputable section

/-! Products and the coefficient-ring Čech augmentation for the original
relative crystalline form complexes. All pairings use native PD forms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (N : SimplicialObject (FormalCoproduct.{u} C))

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.complex H Q π
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.ambientPresheaf Q
local notation "ι" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.augmentationZero H Q π

def total : CochainComplex (ModuleCat.{u} B) ℕ := Presheaf.TotalCup.CechProduct.total N P

def totalCup (a b : ℕ) :
    (total H Q π N).X a →ₗ[B] (total H Q π N).X b →ₗ[B] (total H Q π N).X (a + b) :=
  Presheaf.TotalCup.CechProduct.totalCup N P (Product.sectionPairing H Q π) a b

def cohomologyCup (a b : ℕ) :
    (total H Q π N).homology a →ₗ[B] (total H Q π N).homology b →ₗ[B]
      (total H Q π N).homology (a + b) := by
  refine Presheaf.CohomologyProduct.Cech.cohomologyCup N P (Product.sectionPairing H Q π) ?_ ?_ a b
  · intro i j U V α x y
    exact Product.sectionPairing_natural H Q π i j α x y
  · intro i j U x y
    exact Product.sectionPairing_differential H Q π i j U x y

def coefficientPairing (U : Cᵒᵖ) : (A).obj U →ₗ[B] (A).obj U →ₗ[B] (A).obj U := by
  letI := (Q.obj U.unop).base.toAlgebra
  exact LinearMap.mul B (Q.obj U.unop).ring

theorem coefficientPairing_natural {U V : Cᵒᵖ} (α : U ⟶ V) (x y : (A).obj U) :
    (A).map α (coefficientPairing Q U x y) =
      coefficientPairing Q V ((A).map α x) ((A).map α y) :=
  (Q.map α.unop).ringMap.toRingHom.map_mul x y

def coefficientComplex : CochainComplex (ModuleCat.{u} B) ℕ :=
  Presheaf.AugmentationProduct.source N A

def coefficientCup (a b : ℕ) :
    (coefficientComplex Q N).X a →ₗ[B] (coefficientComplex Q N).X b →ₗ[B]
      (coefficientComplex Q N).X (a + b) :=
  Presheaf.AugmentationProduct.sourceCup N A (coefficientPairing Q) a b

def coefficientCohomologyCup (a b : ℕ) :
    (coefficientComplex Q N).homology a →ₗ[B] (coefficientComplex Q N).homology b →ₗ[B]
      (coefficientComplex Q N).homology (a + b) :=
  Presheaf.AugmentationCohomology.Product.sourceCohomologyCup N A (coefficientPairing Q)
    (coefficientPairing_natural Q) a b

theorem augmentation_closed : ι ≫ (P).d 0 1 = 0 := by
  rw [ModuleComplex.complex_d]
  exact ModuleComplex.augmentationZero_differential H Q π

def augmentation : coefficientComplex Q N ⟶ total H Q π N :=
  Presheaf.AugmentationProduct.map N P A ι (augmentation_closed H Q π)

theorem augmentation_cup (a b : ℕ)
    (x : (coefficientComplex Q N).X a) (y : (coefficientComplex Q N).X b) :
    (augmentation H Q π N).f (a + b) (coefficientCup Q N a b x y) =
      totalCup H Q π N a b ((augmentation H Q π N).f a x) ((augmentation H Q π N).f b y) :=
  Presheaf.AugmentationProduct.map_cup N P A ι (augmentation_closed H Q π)
    (Product.sectionPairing H Q π) (coefficientPairing Q)
    (Product.augmentationZero_mul H Q π) a b x y

theorem augmentation_cohomologyCup (a b : ℕ)
    (x : (coefficientComplex Q N).homology a) (y : (coefficientComplex Q N).homology b) :
    HomologicalComplex.homologyMap (augmentation H Q π N) (a + b)
        (coefficientCohomologyCup Q N a b x y) =
      cohomologyCup H Q π N a b
        (HomologicalComplex.homologyMap (augmentation H Q π N) a x)
        (HomologicalComplex.homologyMap (augmentation H Q π N) b y) := by
  exact Presheaf.AugmentationCohomology.Product.cohomologyMap_cup N A (coefficientPairing Q)
    (coefficientPairing_natural Q) P ι (augmentation_closed H Q π)
    (Product.sectionPairing H Q π)
    (fun i j {U V} α s t => Product.sectionPairing_natural H Q π i j α s t)
    (fun i j U s t => Product.sectionPairing_differential H Q π i j U s t)
    (fun U s t => Product.augmentationZero_mul H Q π U s t) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.CechProduct
