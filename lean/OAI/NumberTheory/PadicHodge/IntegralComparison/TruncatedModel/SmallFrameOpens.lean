import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameClosed

/-! # Small Frame Opens -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrameOpens

noncomputable section

/-! The native small crystalline frame has exactly the original
special-fiber open as its image. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

theorem opensRange : ((SmallFrame.functor p k n X Y f hp).obj U).immersion.opensRange =
    f ⁻¹ᵁ U.val := by
  apply TopologicalSpace.Opens.ext
  exact FrameClosed.range p k n X Y f hp U.val U.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrameOpens
