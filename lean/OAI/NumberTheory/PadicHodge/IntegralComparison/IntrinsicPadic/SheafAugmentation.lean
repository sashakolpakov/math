import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationNormalization

/-! # Sheaf Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafAugmentation.Intrinsic

noncomputable section

/-! The literal global sheaf augmentation is the multiplicative coefficient
augmentation after its actual sheafification unit. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

def coefficientAugmentation : A ⟶ (C).X 0 := (S).map ((a).f 0)

def unitMap : C ⟶ KK := Sheafified.CochainUnit.Pairing.unit.{1,0,1} JT CR C

def augmentation : A ⟶ (KK).X 0 :=
  coefficientAugmentation p X Y f hp n ≫ (unitMap p X Y f hp n).f 0

theorem zero : (b).f 0 = (Bounded.RelativeSheafComplex.structureIso w n).inv ≫
    (SH).map ((a).f 0) :=
  Single.ComplexTransport.map_zero SH (Bounded.RelativeSheafComplex.structureIso w n) a

theorem normalization : Bounded.SheafAugmentationNormalization.structureMap w n ≫
    ((b).f 0).hom = augmentation p X Y f hp n :=
  AdjunctionAugmentationNormalization.normalization
    (sheafificationAdjunction JT (ModuleCat.{1} CR))
    (Bounded.RelativeSheafComplex.structureIso w n)
    (Bounded.SheafAugmentationNormalization.structureMap w n)
    (Bounded.SheafAugmentationNormalization.structureMap_unit w n)
    (coefficientAugmentation p X Y f hp n) ((b).f 0) (zero p X Y f hp n)

theorem coefficient_multiplication (T : Dᵒᵖ) (x y : (A).obj T) :
    (coefficientAugmentation p X Y f hp n).app T
        (BoundedFrame.SheafAugmentationProduct.ambientPairing w n T x y) =
      Crystalline.SheafComplexProduct.coefficientPairing W L μ 0 0 T
        ((coefficientAugmentation p X Y f hp n).app T x)
        ((coefficientAugmentation p X Y f hp n).app T y) := by
  apply ULift.ext
  exact AugmentationProduct.Intrinsic.augmentation_product p X Y f hp n T x.down y.down

theorem multiplication (T : Dᵒᵖ) (x y : (A).obj T) :
    (augmentation p X Y f hp n).app T
        (BoundedFrame.SheafAugmentationProduct.ambientPairing w n T x y) =
      SheafProduct.Intrinsic.sectionPairing p X Y f hp n 0 0 T
        ((augmentation p X Y f hp n).app T x)
        ((augmentation p X Y f hp n).app T y) :=
  (congrArg (((unitMap p X Y f hp n).f 0).app T)
    (coefficient_multiplication p X Y f hp n T x y)).trans
    (SheafProduct.Intrinsic.unit_pairing p X Y f hp n 0 0 T
      ((coefficientAugmentation p X Y f hp n).app T x)
      ((coefficientAugmentation p X Y f hp n).app T y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafAugmentation.Intrinsic
