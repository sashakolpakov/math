import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.GeometricRestriction

/-! # Frame Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestriction.IntrinsicPadicFrameGeometricRestriction

noncomputable section

/-! The actual integral section-ring pullback commutes with the
original section restrictions on a compatible pair of affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (U U' : X₂.left.affineOpens) (V V' : X₁.left.affineOpens)
  (hU : U ⟶ U') (hV : V ⟶ V')
  (hu : V.val ≤ u.left ⁻¹ᵁ U.val) (hu' : V'.val ≤ u.left ⁻¹ᵁ U'.val)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData

theorem integral_square (x : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U'.val) :
    FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X₁ V.val V'.val (leOfHom hV)
      (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U'.val V'.val hu' x) =
    FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U.val V.val hu
      (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X₂ U.val U'.val (leOfHom hU) x) := by
  change (X₁.left.presheaf.map (homOfLE (leOfHom hV)).op)
      ((u.left.appLE U'.val V'.val hu') x) =
    (u.left.appLE U.val V.val hu)
      ((X₂.left.presheaf.map (homOfLE (leOfHom hU)).op) x)
  exact ConcreteCategory.congr_hom (Section.GeometricRestriction.SectionGeometricRestriction.square u.left
    U.val U'.val V.val V'.val (leOfHom hU) (leOfHom hV) hu hu') x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestriction.IntrinsicPadicFrameGeometricRestriction
