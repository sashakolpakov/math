import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData

/-! # Restriction Laws -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RestrictionLaws.IntrinsicPadicRestrictionLaws

noncomputable section

/-! Identity and composition for the actual integral section restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData
variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p])))

theorem id (U : X.left.Opens) (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U) :
    FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U U le_rfl a = a := by
  change (X.left.presheaf.map (𝟙 (op U))).hom a = a
  rw [X.left.presheaf.map_id]
  rfl

theorem comp (U V T : X.left.Opens) (hUV : U ≤ V) (hVT : V ≤ T)
    (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X T) :
    FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U T (hUV.trans hVT) a =
      FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X V T hVT a) := by
  change (X.left.presheaf.map (homOfLE (hUV.trans hVT)).op).hom a =
    (X.left.presheaf.map (homOfLE hUV).op).hom
      ((X.left.presheaf.map (homOfLE hVT).op).hom a)
  rw [show (homOfLE (hUV.trans hVT)).op = (homOfLE hVT).op ≫ (homOfLE hUV).op from Subsingleton.elim _ _,
    X.left.presheaf.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RestrictionLaws.IntrinsicPadicRestrictionLaws
