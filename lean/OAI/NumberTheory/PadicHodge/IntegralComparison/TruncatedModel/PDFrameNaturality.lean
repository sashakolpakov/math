import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.BoundedFrameIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PDIntrinsicCoordinates

/-! # PD Frame Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PDFrameNaturality

noncomputable section

/-! The actual small-to-bounded PD coordinate comparison is natural
under the normalized native frame isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
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

theorem naturality : (Small.PDComplexCoordinates.originalFunctor p k Y).map e.hom.op ≫
    (Small.PDIntrinsicCoordinates.Intrinsic.iso p k Y).hom.app
      (op ((SmallFrame.smallFunctor p k n X₂ Y f₂ hp₂).obj U₂)) =
    (Small.PDIntrinsicCoordinates.Intrinsic.iso p k Y).hom.app
      (op ((SmallFrame.smallFunctor p k n X₁ Y f₁ hp₁).obj U₁)) ≫
    (GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded (Witt.Crystalline.wittStructureMap p k Y) n).map
      (BoundedFrameIso.iso p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ e).hom.op := by
  let a := GeometricComparison.SmallCrystallineEquivalence.SmallCrystallineAdapter.to62FullyFaithful.preimage e.hom
  have h := (Small.PDIntrinsicCoordinates.Intrinsic.iso p k Y).hom.naturality a.op
  change (Small.PDComplexCoordinates.originalFunctor p k Y).map
      (GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.map a).op ≫ _ = _ at h
  have ha : GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62.map a = e.hom :=
    GeometricComparison.SmallCrystallineEquivalence.SmallCrystallineAdapter.to62FullyFaithful.map_preimage e.hom
  rw [ha] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PDFrameNaturality
