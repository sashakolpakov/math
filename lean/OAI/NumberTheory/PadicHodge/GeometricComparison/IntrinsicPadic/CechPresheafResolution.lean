import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PresheafResolutionAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total

/-! # Cech Presheaf Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution

noncomputable section

/-! The original native frame augmentations assemble into a canonical map
from the crystalline structure presheaf to their actual Čech total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "JW" => Ideal.span {(p : W)}
local notation "PS" => (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := JW) (δ := OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n)ᵒᵖ ⥤ ModuleCat W

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def source : CochainComplex PS ℕ := (CochainComplex.single₀ PS).obj
  ((IntegralComparison.BoundedCrystalline.Site.inclusion w n).op ⋙ IntegralComparison.BigCrystallineCohomology.modulePresheaf w)

def diagram : X.left.affineOpensᵒᵖ ⥤ CochainComplex PS ℕ :=
  (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n

def cone : (Functor.const X.left.affineOpensᵒᵖ).obj (source p Y n) ⟶ diagram p X Y f hp n :=
  Functor.whiskerLeft (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op
    (Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.augmentation w n)

variable {ι : Type} (U : ι → X.left.affineOpens)

def total : CochainComplex PS ℕ := CechCone.Total.CechConeTotal.total U (diagram p X Y f hp n)

def augmentation : source p Y n ⟶ total p X Y f hp n U :=
  CechCone.Total.CechConeTotal.augmentation U (diagram p X Y f hp n) (source p Y n) (cone p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution
