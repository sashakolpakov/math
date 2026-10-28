import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSliceMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.PresheafResolutionAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction

/-! # Presheaf Slice Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PresheafSliceDiagram.IntrinsicPadicPresheafSliceDiagram

noncomputable section

/-! The actual native presheaf-resolution diagram contracts on a slice
over each member of its affine covering family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) (I : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "FI" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def diagram : X.left.affineOpensᵒᵖ ⥤
    CochainComplex ((Over FI)ᵒᵖ ⥤ ModuleCat (WittVector p (ZMod p))) ℕ :=
  (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).op ⋙
    BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n ⋙
      (IntegralComparison.Relative.ComplexRestriction.restriction (B := WittVector p (ZMod p))
        (Over.forget FI)).mapHomologicalComplex (.up ℕ)

omit [IsSeparated Y.hom] in
theorem restriction_eq (V : X.left.affineOpens) :
    (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).map (homOfLE (inf_le_left : V ⊓ I ≤ V)) =
      LocalProduct.IntrinsicPadicLocalProduct.restriction p X Y f hp n V.val I.val V.property I.property := rfl

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    ((diagram p X Y f hp n I).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := by
  dsimp only [diagram, Functor.comp_map, Functor.op_map]
  rw [Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.map_eq]
  erw [restriction_eq]
  exact FrameSliceMap.IntrinsicPadicFrameSliceMap.isIso p X Y f hp n V.val I.val V.property I.property

variable {ι : Type} (U : ι → X.left.affineOpens) (i : ι)

def localHomotopyEquiv :=
  Semilattice.LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv X.left.affineOpens U i
    (diagram p X Y f hp n (U i)) (fun V => meet_isIso p X Y f hp n (U i) V)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PresheafSliceDiagram.IntrinsicPadicPresheafSliceDiagram
