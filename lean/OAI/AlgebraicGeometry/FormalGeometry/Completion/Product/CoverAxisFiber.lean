import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.EtaleProductCoverConnected
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductAxis

/-! # Cover Axis Fiber -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverAxisFiber.Construction

noncomputable section

/-! Pulling a product cover back to the first axis gives its actual family fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S A B T : Scheme.{u}} (p : A ⟶ S) (q : B ⟶ S)
  (t : T ⟶ pullback p q) (b : S ⟶ B) (hb : b ≫ q = 𝟙 S)

/-- The literal axis base change is the family base change at the given base section. -/
def productCoverFirstAxisFiberIso :
    pullback t (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left ≅
      pullback (t ≫ pullback.snd p q) b :=
  ((IsPullback.of_hasPullback t (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left).paste_vert
    (Proper.ProductAxis.Construction.properProductFirstAxis_isPullback (Over.mk p) (Over.mk q) b hb)).isoPullback

variable {K : Type u} [Field K] [IsAlgClosed K] {A B T : Scheme.{u}}
  [IsIntegral A] [IsIntegral B]
  (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
  (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
  (t : T ⟶ pullback p q) [IsFinite t] [Etale t]
  [IsIso (t ≫ pullback.snd p q).fromNormalization]
  (b : Spec (CommRingCat.of K) ⟶ B) (hb : b ≫ q = 𝟙 _)

/-- The actual first-axis base change is connected once the normalization is the second factor. -/
theorem productCover_firstAxis_connected :
    ConnectedSpace (pullback t (Proper.ProductAxis.Construction.properProductFirstAxisOver (Over.mk p) (Over.mk q) b hb).left : Scheme.{u}) := by
  have := Finite.EtaleProductCoverConnected.Construction.finiteEtaleProductCover_rational_fiber_connected p q t b hb
  exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (productCoverFirstAxisFiberIso p q t b hb))).connectedSpace_iff.mpr inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverAxisFiber.Construction
