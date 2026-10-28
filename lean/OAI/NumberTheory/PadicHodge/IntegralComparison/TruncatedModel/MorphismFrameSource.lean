import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameDiagramPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameDiagonalMap

/-! # Morphism Frame Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameSource

noncomputable section

/-! Actual geometric frame pullback on the original native source
complexes, with their existing crystalline coefficient functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))}
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y₁ f₁ hp₁
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y₂ f₂ hp₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram.transformation p k n u v f₁ f₂ hp₁ hp₂ sq
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.DeRham.Comparison.coefficientFunctor p k

def transformation : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ FrameDiagonalMap.source p k n X₂ Y₂ f₂ hp₂ ⟶
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ FrameDiagonalMap.source p k n X₁ Y₁ f₁ hp₁ :=
  Functor.whiskerRight
    (GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.transformation v.left (MorphismData.Frames.ambient_over p k v) n P Q a)
    ((H).mapHomologicalComplex (.up ℕ))

theorem component (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    (transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (Opposite.op U) =
      ((H).mapHomologicalComplex (.up ℕ)).map
        (RelativeFrame.ChangeNaturality.frameMap ((Q).obj U).obj
          ((BoundedOpen.Equivalence.postcompose v.left (MorphismData.Frames.ambient_over p k v) n).obj ((P).obj U)).obj
          ((a).app U).hom) :=
  congrArg ((H).mapHomologicalComplex (.up ℕ)).map
    (GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.component v.left (MorphismData.Frames.ambient_over p k v) n P Q a U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameSource
