import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConeProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechMap

/-! # Frame Sheaf Product Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap.Intrinsic

noncomputable section

/-! The actual frame-total map remains multiplicative after the native
coefficient lift, crystalline sheafification, and bounded Čech augmentation. -/

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

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.complex p X Y f hp n
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.map p X Y f hp n
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing p X Y f hp n
local notation "hμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing_natural p X Y f hp n
local notation "σ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProductMap.Intrinsic.cup p X Y f hp n

local instance monoidal : ((JT).W (A := ModuleCat.{1} CR)).IsMonoidal :=
  Module.SheafTensor.monoidal JT CR

def source := Crystalline.ConeProduct.coefficientSource W M

def map := Crystalline.ConeProduct.map W JT M L a

def sourcePairing := Crystalline.ConeProduct.sourcePairing W M σ

abbrev map_pairing := Crystalline.ConeProduct.map_pairing W JT M L a μ hμ σ
  (FrameProductMap.Intrinsic.map_cup p X Y f hp n)

variable {ι : Type} [Finite ι]
  (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n)

def cechMap := Presheaf.ConeCechMap.map CR F
  (source p X Y f hp n)
  (SheafProduct.Intrinsic.underlyingComplex p X Y f hp n)
  (Intrinsic.map p X Y f hp n)

abbrev cechMap_cup := Presheaf.ConeCechMap.map_cup CR F
  (source p X Y f hp n)
  (SheafProduct.Intrinsic.underlyingComplex p X Y f hp n)
  (Intrinsic.map p X Y f hp n)
  (SheafProduct.Intrinsic.sectionPairing p X Y f hp n)
  (sourcePairing p X Y f hp n)
  (map_pairing p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap.Intrinsic
