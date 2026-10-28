import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.DiagramPullback

/-! # Morphism Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution

noncomputable section

/-! A morphism of actual truncated models induces an augmented map of
their original bounded crystalline resolution diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  v.left (MorphismData.Frames.ambient_over p k v) n
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left ⋙
  FrameFunctor.functor p k n X₁ Y₁ f₁ hp₁
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left ⋙
  FrameFunctor.functor p k n X₂ Y₂ f₂ hp₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram.transformation p k n u v f₁ f₂ hp₁ hp₂ sq

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def transformation : (Q).op ⋙ GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n ⋙
    (R).mapHomologicalComplex (.up ℕ) ⟶ (P).op ⋙ GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n :=
  GeometricComparison.BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback.transformation v.left (MorphismData.Frames.ambient_over p k v)
    n P Q a

theorem augmentation (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    BoundedFrame.PullbackAugmentation.augmentation v.left
      (MorphismData.Frames.ambient_over p k v) n ((Q).obj U) ≫
        (transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (op U) =
    Bounded.RelativeSheafComplex.augmentation w₁ n ((P).obj U) :=
  GeometricComparison.BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback.augmentation v.left (MorphismData.Frames.ambient_over p k v)
    n P Q a U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismResolution
