import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRingSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FrameSquare

/-! # Frame Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameNaturality.IntrinsicPadicFrameGeometricNaturality

noncomputable section

/-! Actual geometric frame maps commute with affine restrictions. -/

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
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose v.left (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare
  U.val V.val U.property V.property hu n
local notation "a'" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameMap.IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare
  U'.val V'.val U'.property V'.property hu' n

theorem natural : (G).map ((P).map hV) ≫ a' = a ≫ (Q).map hU :=
  Bounded.FrameSquare.BoundedGeometricFrameSquare.square v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
    ((P).map hV) ((Q).map hU) a a'
    (FrameRingSquare.IntrinsicPadicFrameGeometricRingSquare.ringHom p u v f₁ f₂ hp₁ hp₂ hsquare U U' V V' hU hV hu hu' n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameNaturality.IntrinsicPadicFrameGeometricNaturality
