import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingPullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalComplex

/-! # Morphism Rings -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRings

noncomputable section

/-! The actual native frame rings pull back naturally over
compatible affine pairs of an integral-model geometric square. -/

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

def transformation : (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target u.left).op ⋙ PrincipalComplex.Comparison.rings p k n X₂ Y₂ f₂ hp₂ ⟶
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source u.left).op ⋙ PrincipalComplex.Comparison.rings p k n X₁ Y₁ f₁ hp₁ :=
  GeometricComparison.Crystalline.FrameRingPullback.CrystallineFrameRingPullback.transformation v.left (MorphismData.Frames.ambient_over p k v) n P Q a

theorem component (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    (transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (Opposite.op U) =
      (GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded w₂ n).map ((a).app U).op :=
  GeometricComparison.Crystalline.FrameRingPullback.CrystallineFrameRingPullback.component v.left (MorphismData.Frames.ambient_over p k v) n P Q a U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRings
