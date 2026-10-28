import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame
import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineEquivalence

/-! # Bounded Frame Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFrameIso

noncomputable section

/-! Isomorphisms of the original small model frames lift to their actual
bounded frames without changing the ambient ring maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X₁.hom] [Smooth X₂.hom]
  (Y : Over (Spec (CommRingCat.of k)))
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (e : (SmallFrame.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (SmallFrame.functor p k n X₁ Y f₁ hp₁).obj U₁)

def iso : (FrameFunctor.functor p k n X₂ Y f₂ hp₂).obj U₂ ≅
    (FrameFunctor.functor p k n X₁ Y f₁ hp₁).obj U₁ :=
  (BoundedCrystalline.Site.property (Witt.Crystalline.wittStructureMap p k Y) n).isoMk
    (BigCrystallineSite.fromSmall.mapIso
      (GeometricComparison.SmallCrystallineEquivalence.SmallCrystallineAdapter.to62FullyFaithful.preimageIso e))

theorem hom_apply (a : Γ(X₁.left, U₁.val)) :
    (iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom.hom.ringMap a = e.hom.ambientMap a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFrameIso
