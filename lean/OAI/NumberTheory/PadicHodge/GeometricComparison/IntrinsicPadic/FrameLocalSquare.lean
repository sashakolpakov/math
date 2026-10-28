import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.PDTruncationCore

/-! # Frame Local Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLocalSquare.IntrinsicPadicFrameGeometricLocalSquare

noncomputable section

/-! The native local frame square is the prime-power truncation of
the actual integral section-ring restriction square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (U U' : X₂.left.affineOpens) (V V' : X₁.left.affineOpens)
  (hU : U ⟶ U') (hV : V ⟶ V')
  (hu : V.val ≤ u.left ⁻¹ᵁ U.val) (hu' : V'.val ≤ u.left ⁻¹ᵁ U'.val) (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData

local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₁ V.val
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₁ V'.val
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U.val
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X₂ U'.val
local notation "W" => WittVector p (ZMod p)

local instance padicA : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₁ V.val
local instance padicB : Algebra ℤ_[p] B := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₁ V'.val
local instance padicC : Algebra ℤ_[p] C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₂ U.val
local instance padicD : Algebra ℤ_[p] D := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X₂ U'.val
local instance wittA : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance wittB : Algebra W B := WittAlgebra.PadicWittAlgebra.algebra p B
local instance wittC : Algebra W C := WittAlgebra.PadicWittAlgebra.algebra p C
local instance wittD : Algebra W D := WittAlgebra.PadicWittAlgebra.algebra p D

theorem square :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X₁ Y₁ f₁ hp₁ V.val V'.val V.property V'.property (leOfHom hV) n).hom.ringMap.toRingHom.comp
      (FrameMap.IntrinsicPadicFrameGeometricMap.localMap p u v f₁ f₂ hp₁ hp₂ hsquare U'.val V'.val U'.property V'.property hu' n).hom.ringMap.toRingHom =
    (FrameMap.IntrinsicPadicFrameGeometricMap.localMap p u v f₁ f₂ hp₁ hp₂ hsquare U.val V.val U.property V.property hu n).hom.ringMap.toRingHom.comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X₂ Y₂ f₂ hp₂ U.val U'.val U.property U'.property (leOfHom hU) n).hom.ringMap.toRingHom := by
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₁ V.val V.property
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₁ V'.val V'.property
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₂ U.val U.property
  let := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X₂ U'.val U'.property
  exact PDTruncationCore.PDTruncationSquare.square
    (GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.integralDPMap p (ZMod p) B A
      (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X₁ V.val V'.val (leOfHom hV)))
    (GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.integralDPMap p (ZMod p) C A (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U.val V.val hu))
    (GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.integralDPMap p (ZMod p) D B (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u U'.val V'.val hu'))
    (GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.integralDPMap p (ZMod p) D C
      (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X₂ U.val U'.val (leOfHom hU))) n
    (FrameRestriction.IntrinsicPadicFrameGeometricRestriction.integral_square p u U U' V V' hU hV hu hu')

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLocalSquare.IntrinsicPadicFrameGeometricLocalSquare
