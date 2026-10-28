import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IntrinsicAugmentationEdge

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Augmentation.IntrinsicIntrinsic

noncomputable section

/-! The actual global-model augmentation induces its product-preserving
native crystalline Čech map, with the literal balanced comparison edge. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "FF" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) (f := w) (n := n)

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing p X Y f hp n
local notation "hμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing_natural p X Y f hp n
local notation "dμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing_differential p X Y f hp n

local instance monoidal : ((BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n).W (A := ModuleCat.{1} CR)).IsMonoidal :=
  Module.SheafTensor.monoidal (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) CR

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "SH" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.coefficientComplex p X Y f hp n
local notation "KK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.underlyingComplex p X Y f hp n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct.ambient
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.augmentation p X Y f hp n

local notation "aK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafAugmentation.Intrinsic.augmentation p X Y f hp n
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

theorem original_closed : ((b).f 0).hom ≫ (KK).d 0 1 = 0 :=
  congrArg (fun c : O ⟶ (K).X 1 => c.hom)
    (Augmented.ResolutionCycles.augmentation_condition K b)

theorem closed : aK ≫ (KK).d 0 1 = 0 := by
  erw [← SheafAugmentation.Intrinsic.normalization, Category.assoc,
    original_closed, comp_zero]

variable {ι : Type} (F : ι → BoundedCrystalline.Site.Objects (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n)
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F

local instance coefficientProducts : HasProducts.{0} (ModuleCat.{1} CR) :=
  fun T => (ModuleCat.hasLimitsOfSize.{0,0,1,1}).has_limits_of_shape (Discrete T)

def totalMap : Presheaf.AugmentationProduct.source (R := CR) N A ⟶
    Presheaf.TotalCup.CechProduct.total (R := CR) N KK := Presheaf.AugmentationProduct.map.{1,0,0,1,1} (R := CR)
  N KK A aK (closed p X Y f hp n)

theorem totalMap_cup (i j : ℕ)
    (x : (Presheaf.AugmentationProduct.source N A).homology i)
    (y : (Presheaf.AugmentationProduct.source N A).homology j) :
    HomologicalComplex.homologyMap (totalMap p X Y f hp n F) (i + j)
      (Presheaf.AugmentationCohomology.Product.sourceCohomologyCup N A
        (BoundedFrame.SheafAugmentationProduct.ambientPairing w n)
        (BoundedFrame.SheafAugmentationProduct.ambientPairing_natural w n) i j x y) =
      Presheaf.CohomologyProduct.Cech.cohomologyCup N KK
        (SheafProduct.Intrinsic.sectionPairing p X Y f hp n)
        (SheafProduct.Intrinsic.sectionPairing_natural p X Y f hp n)
        (SheafProduct.Intrinsic.sectionPairing_differential p X Y f hp n) i j
        (HomologicalComplex.homologyMap (totalMap p X Y f hp n F) i x)
        (HomologicalComplex.homologyMap (totalMap p X Y f hp n F) j y) := by
  exact Presheaf.AugmentationCohomology.Product.cohomologyMap_cup.{1,0,0,1,1} (R := CR)
    N A (BoundedFrame.SheafAugmentationProduct.ambientPairing w n)
    (BoundedFrame.SheafAugmentationProduct.ambientPairing_natural w n)
    KK aK (closed p X Y f hp n)
    (SheafProduct.Intrinsic.sectionPairing p X Y f hp n)
    (SheafProduct.Intrinsic.sectionPairing_natural p X Y f hp n)
    (SheafProduct.Intrinsic.sectionPairing_differential p X Y f hp n)
    (SheafAugmentation.Intrinsic.multiplication p X Y f hp n) i j x y

def edge : (NonemptyCechNerve.complexFunctor F).obj (O).obj ⟶
    Presheaf.TotalCup.CechProduct.total (R := CR) N KK :=
  FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge.{1,0} F CR JT K b

theorem edge_eq : edge p X Y f hp n F =
    Presheaf.AugmentationProduct.map.{1,0,0,1,1}
      N KK (O).obj ((b).f 0).hom (original_closed p X Y f hp n) :=
  (Presheaf.AugmentationEdge.map_eq_edge.{1,0,0,1,1}
    N KK (O).obj ((b).f 0).hom (original_closed p X Y f hp n)).symm

theorem square : (BoundedFrame.CechComplex.presheafIso w n F).hom ≫
    edge p X Y f hp n F = totalMap p X Y f hp n F := by
  rw [edge_eq]
  exact Presheaf.AugmentationPrecompose.map.{1,0,0,1,1}
    N KK (Bounded.SheafAugmentationNormalization.structureMap w n)
    aK (closed p X Y f hp n) ((b).f 0).hom (original_closed p X Y f hp n)
    (SheafAugmentation.Intrinsic.normalization p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Augmentation.IntrinsicIntrinsic
