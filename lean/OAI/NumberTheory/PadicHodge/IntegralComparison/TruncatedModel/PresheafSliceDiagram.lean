import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.LocalProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction

/-! # Presheaf Slice Diagram -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafSliceDiagram

noncomputable section

/-! The native model-frame diagram contracts on each chart slice. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : X.left.affineOpens)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.AffineModelFrame.frame p k n X Y f hp I.val I.property

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def diagram : X.left.affineOpensᵒᵖ ⥤ CochainComplex ((Over FI)ᵒᵖ ⥤ ModuleCat.{0} (WittVector p k)) ℕ :=
  (FrameFunctor.functor p k n X Y f hp).op ⋙
    GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor w n ⋙
      (Relative.ComplexRestriction.restriction (B := WittVector p k)
        (Over.forget FI)).mapHomologicalComplex (.up ℕ)

omit [IsSeparated Y.hom] in
theorem restriction_eq (V : X.left.affineOpens) :
    (FrameFunctor.functor p k n X Y f hp).map
      (homOfLE (inf_le_left : V ⊓ I ≤ V)) =
        LocalProduct.restriction p k n X Y f hp V.val I.val V.property I.property := rfl

theorem meet_isIso (V : X.left.affineOpens) : IsIso
    ((diagram p k n X Y f hp I).map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op) := by
  dsimp only [diagram, Functor.comp_map, Functor.op_map]
  rw [GeometricComparison.Frame.PresheafResolutionAugmentation.FramePresheafResolutionAugmentation.map_eq]
  erw [restriction_eq]
  exact LocalProduct.sliceMap_isIso p k n X Y f hp V.val I.val V.property I.property

variable {ι : Type} (U : ι → X.left.affineOpens) (i : ι)

def localHomotopyEquiv := GeometricComparison.Semilattice.LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv X.left.affineOpens U i
  (diagram p k n X Y f hp (U i)) (fun V => meet_isIso p k n X Y f hp (U i) V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PresheafSliceDiagram
