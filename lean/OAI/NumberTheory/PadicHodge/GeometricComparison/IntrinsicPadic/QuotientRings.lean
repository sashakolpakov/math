import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex

/-! # Quotient Rings -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientRings.IntrinsicPadicGeometricQuotientRings

noncomputable section

/-! The actual native quotient-frame rings pull back naturally over
compatible affine pairs of an integral-model geometric square. -/

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
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n

def transformation : (Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X₂ Y₂ f₂ hp₂ n ⟶
    (Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X₁ Y₁ f₁ hp₁ n :=
  Crystalline.FrameRingPullback.CrystallineFrameRingPullback.transformation v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a

theorem component (U : Affine.MapPairs.AffineMapPairs.Charts u.left) :
    (transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app (Opposite.op U) =
      (Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded w₂ n).map ((a).app U).op :=
  Crystalline.FrameRingPullback.CrystallineFrameRingPullback.component v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientRings.IntrinsicPadicGeometricQuotientRings
