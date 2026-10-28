import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ChangeOnSliceMap

/-! # Frame Slice Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSliceMap.IntrinsicPadicFrameSliceMap

noncomputable section

/-! The original native frame restriction induces an isomorphism of the
actual presheaf resolutions over every incoming object of the chosen chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (V I : X.left.Opens) (hV : IsAffineOpen V) (hI : IsAffineOpen I)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "FV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I hI n
local notation "FVI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (V ⊓ I) (hV.inf hI) n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

theorem isIso : IsIso
    (((IntegralComparison.Relative.ComplexRestriction.restriction (B := WittVector p (ZMod p))
      (Over.forget FI)).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.Change.presheafMap (LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n V I hV hI))) :=
  Frame.ChangeOnSliceMap.FrameChangeOnSliceMap.isIso w n FI FV FVI (LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n V I hV hI)
    (fun T τ => LocalProduct.IntrinsicPadicLocalProduct.map_isIso p X Y f hp n V I hV hI T τ)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSliceMap.IntrinsicPadicFrameSliceMap
