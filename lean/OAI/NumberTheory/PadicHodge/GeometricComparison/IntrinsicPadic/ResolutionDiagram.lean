import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.DiagramPullback

/-! # Resolution Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram

noncomputable section

/-! Actual compatible integral-model maps induce augmented native
crystalline resolution pullbacks over the category of compatible affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂)
  (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) (Over.Hom.left v) (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def transformation : (Q).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n ⋙
    (R).mapHomologicalComplex (.up ℕ) ⟶ (P).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n :=
  BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback.transformation v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a

theorem augmentation (U : Affine.MapPairs.AffineMapPairs.Charts u.left) :
    IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n ((Q).obj U) ≫
      (transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app (Opposite.op U) =
    IntegralComparison.Bounded.RelativeSheafComplex.augmentation w₁ n ((P).obj U) :=
  BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback.augmentation v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n P Q a U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ResolutionDiagram.IntrinsicPadicGeometricResolutionDiagram
