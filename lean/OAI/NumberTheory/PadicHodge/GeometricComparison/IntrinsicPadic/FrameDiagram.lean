import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs

/-! # Frame Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram

noncomputable section

/-! Actual native frame maps form a natural transformation over all
compatible affine source and target opens of a geometric square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose v.left (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n

def transformation : Affine.MapPairs.AffineMapPairs.source u.left ⋙ P ⋙ G ⟶ Affine.MapPairs.AffineMapPairs.target u.left ⋙ Q where
  app A := FrameMap.IntrinsicPadicFrameGeometricMap.map p u v f₁ f₂ hp₁ hp₂ hsquare
    A.val.2.val A.val.1.val A.val.2.property A.val.1.property A.property n
  naturality A B h := FrameNaturality.IntrinsicPadicFrameGeometricNaturality.natural p u v f₁ f₂ hp₁ hp₂ hsquare
    A.val.2 B.val.2 A.val.1 B.val.1
    ((Affine.MapPairs.AffineMapPairs.target u.left).map h) ((Affine.MapPairs.AffineMapPairs.source u.left).map h)
    A.property B.property n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram
