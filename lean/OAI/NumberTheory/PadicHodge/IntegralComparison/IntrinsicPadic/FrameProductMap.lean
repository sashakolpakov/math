import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.SectionNaturalTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Product
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramCone

/-! # Frame Product Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic

noncomputable section

/-! The actual frame de Rham Čech total maps multiplicatively into
the original global p-adic-model presheaf resolution. -/

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
local notation "BG" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) (f := w) (n := n)

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def transformation : Q ⋙ (Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P :=
  Functor.whiskerLeft (FF).op (GeometricComparison.Frame.SectionNaturalTransformation.FrameSectionNaturalTransformation.transformation w n)

def localPairing (i j : ℕ) (V : X.left.affineOpensᵒᵖ) :
    ((Q).obj V).X i →ₗ[W] ((Q).obj V).X j →ₗ[W] ((Q).obj V).X (i+j) :=
  RelativeFrame.Product.framePairing (((FF).obj V.unop).obj) i j

abbrev complex := Presheaf.TotalCup.CechProduct.total N (Cech.ComplexDiagramCoordinates.complex Q)

abbrev cup := Presheaf.TotalCup.CechProduct.totalCup N
  (Cech.ComplexDiagramCoordinates.complex Q) (localPairing p X Y f hp n)

def map := Cech.PresheafDiagramCone.map W U Q P (transformation p X Y f hp n)

omit [IsProper X.hom] [X.left.IsSeparated] in
theorem local_product (i j : ℕ) (V : X.left.affineOpensᵒᵖ) (T : Dᵒᵖ)
    (x : ((Q).obj V).X i) (y : ((Q).obj V).X j) :
    (((transformation p X Y f hp n).app V).f (i+j)).app T
      (localPairing p X Y f hp n i j V x y) =
        CechProduct.Intrinsic.localPairing p X Y f hp n i j V T
          ((((transformation p X Y f hp n).app V).f i).app T x)
          ((((transformation p X Y f hp n).app V).f j).app T y) :=
  RelativeFrame.Product.map_product
    (BoundedFrame.Diagram.productDiagram ((FF).obj V.unop)) BG
    (BoundedFrame.Diagram.projection ((FF).obj V.unop)) (((FF).obj V.unop).obj)
    (BoundedFrame.Symbols.frameProjection ((FF).obj V.unop)) T.unop i j x y

abbrev map_cup := Cech.PresheafDiagramCone.map_cup W U Q P
  (transformation p X Y f hp n) (localPairing p X Y f hp n)
  (CechProduct.Intrinsic.localPairing p X Y f hp n)
  (local_product p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic
