import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramAugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.CechProduct

/-! # Augmentation Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AugmentationProduct.Intrinsic

noncomputable section

/-! The original global p-adic-model crystalline augmentation
preserves its genuine PD wedge and Čech product. -/

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

local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.source p Y n
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.cone p X Y f hp n

def sourcePairing (T : Dᵒᵖ) : ((M).X 0).obj T →ₗ[W] ((M).X 0).obj T →ₗ[W] ((M).X 0).obj T :=
  RelativeCrystalline.CechProduct.coefficientPairing Q T

omit [IsProper X.hom] [X.left.IsSeparated] in
theorem local_multiplication (V : X.left.affineOpensᵒᵖ) (T : Dᵒᵖ)
    (x y : ((M).X 0).obj T) :
    (((η).app V).f 0).app T (sourcePairing p Y n T x y) =
      CechProduct.Intrinsic.localPairing p X Y f hp n 0 0 V T
        ((((η).app V).f 0).app T x) ((((η).app V).f 0).app T y) := by
  change ((RelativeCrystalline.ModuleComplex.augmentation
    (BoundedFrame.Diagram.productDiagram ((FF).obj V.unop)) Q
    (BoundedFrame.Diagram.projection ((FF).obj V.unop))).f 0).app T _ = _
  rw [RelativeCrystalline.ModuleComplex.augmentation_zero]
  exact RelativeCrystalline.Product.augmentationZero_mul
    (BoundedFrame.Diagram.productDiagram ((FF).obj V.unop)) Q
    (BoundedFrame.Diagram.projection ((FF).obj V.unop)) T x y

abbrev augmentation_product := Cech.PresheafDiagramAugmentationProduct.augmentation_product
  W U P M η (CechProduct.Intrinsic.localPairing p X Y f hp n)
  (sourcePairing p Y n) (local_multiplication p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AugmentationProduct.Intrinsic
