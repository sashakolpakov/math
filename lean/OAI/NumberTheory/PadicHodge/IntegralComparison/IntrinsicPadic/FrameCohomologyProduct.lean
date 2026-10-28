import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CochainCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BalancedProduct

/-! # Frame Cohomology Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameCohomologyProduct.Intrinsic

noncomputable section

/-! The actual frame-total map remains multiplicative after the native
coefficient lift, crystalline sheafification, and bounded Čech augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
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

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n
local notation "MM" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap.Intrinsic.source p X Y f hp n
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameSheafProductMap.Intrinsic.sourcePairing p X Y f hp n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison.frames p X Y f hp n
local notation "KK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.underlyingComplex p X Y f hp n
local notation "μK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.sectionPairing p X Y f hp n
local notation "hK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.sectionPairing_natural p X Y f hp n
local notation "dK" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic.sectionPairing_differential p X Y f hp n

abbrev differential := Crystalline.CochainCup.differential W M σ
  (Frame.DiagramProduct.differential_cup w H U)

def cup := Cochain.CohomologyCup.cohomologyCup MM ν (differential p X Y f hp n)

abbrev map := FrameSheafProductMap.Intrinsic.cechMap p X Y f hp n F

abbrev map_cup := Presheaf.ConeCechCohomology.map_cup CR F MM KK
  (FrameSheafProductMap.Intrinsic.map p X Y f hp n)
  μK hK dK ν (differential p X Y f hp n)
  (FrameSheafProductMap.Intrinsic.map_pairing p X Y f hp n)

def comparison (i : ℕ) := (BalancedProduct.Intrinsic.comparison p X Y f hp n i).comp
  (HomologicalComplex.homologyMap (Intrinsic.map p X Y f hp n) i).hom

theorem comparison_cup (i j : ℕ) (x : (MM).homology i) (y : (MM).homology j) :
    comparison p X Y f hp n (i+j) (cup p X Y f hp n i j x y) =
      BalancedBounded.CechCup.cup p (ZMod p) w n F
        (GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.cover p X Y f hp n) i j
        (comparison p X Y f hp n i x) (comparison p X Y f hp n j y) :=
  (congrArg (BalancedProduct.Intrinsic.comparison p X Y f hp n (i+j))
    (map_cup p X Y f hp n i j x y)).trans
      (BalancedProduct.Intrinsic.comparison_cup p X Y f hp n i j _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameCohomologyProduct.Intrinsic
