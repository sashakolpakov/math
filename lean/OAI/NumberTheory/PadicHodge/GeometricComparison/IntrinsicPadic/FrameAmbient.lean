import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerIdeal

/-! # Frame Ambient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameAmbient.IntrinsicPadicFrameAmbient

noncomputable section

/-! The ambient maps of the native integral affine frames are the open
immersions of the actual prime-power closed-subscheme charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V) (n : ℕ)

def map : Spec (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.ring ⟶
    Spec (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n).obj.ring :=
  Spec.map (CommRingCat.ofHom (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom)

theorem map_eq : IntrinsicPadicFrameAmbient.map p X Y f hp U V hU hV hUV n =
    (PrimePowerIdeal.PrimePowerIdealSheaf.ideal X.left p n).glueDataObjMap
      (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) hUV := by
  change Spec.map (CommRingCat.ofHom (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom) = _
  rw [PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap]
  rfl

theorem openImmersion : IsOpenImmersion (IntrinsicPadicFrameAmbient.map p X Y f hp U V hU hV hUV n) := by
  rw [map_eq]
  exact IdealQuotientMaps.IdealQuotientOpenMaps.openImmersion (PrimePowerIdeal.PrimePowerIdealSheaf.ideal X.left p n)
    (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) hUV

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameAmbient.IntrinsicPadicFrameAmbient
