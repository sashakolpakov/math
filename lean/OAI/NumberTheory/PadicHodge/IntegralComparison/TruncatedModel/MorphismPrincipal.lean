import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismRings
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameDiagramPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameSquare

/-! # Morphism Principal -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPrincipal.Comparison

noncomputable section

/-! The original native principal PD-to-ordinary comparison commutes
with actual geometric pullback on compatible affine pairs. -/

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

local notation "S" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u))
local notation "T" => Functor.op (OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u))
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "W" => WittVector p k

def frameMap : T ⋙ PrincipalComplex.Comparison.pdComplexes p k n X₂ Y₂ f₂ hp₂ ⟶
    S ⋙ PrincipalComplex.Comparison.pdComplexes p k n X₁ Y₁ f₁ hp₁ :=
  GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.transformation v.left (MorphismData.Frames.ambient_over p k v) n P Q a

theorem natural : frameMap p k n u v f₁ f₂ hp₁ hp₂ sq ≫
    Functor.whiskerLeft S (PrincipalComplex.Comparison.iso p k n X₁ Y₁ f₁ hp₁).hom =
      Functor.whiskerLeft T (PrincipalComplex.Comparison.iso p k n X₂ Y₂ f₂ hp₂).hom ≫
        Functor.whiskerRight (MorphismRings.transformation p k n u v f₁ f₂ hp₁ hp₂ sq)
          (OrdinaryDeRhamFunctor.Ordinary.functor W) := by
  apply NatTrans.ext
  funext U
  have h₁ := GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback.component v.left (MorphismData.Frames.ambient_over p k v) n P Q a U.unop
  have h₂ := GeometricComparison.PrincipalFrameSquare.PrincipalGeometricFrameSquare.square (p : W) γ v.left (MorphismData.Frames.ambient_over p k v) n
    ((P).obj U.unop) ((Q).obj U.unop) ((a).app U.unop)
    (PrincipalComplex.Comparison.ideal_generated p k n X₁ Y₁ f₁ hp₁ (Opposite.op U.unop.val.1))
    (PrincipalComplex.Comparison.ideal_generated p k n X₂ Y₂ f₂ hp₂ (Opposite.op U.unop.val.2))
  have h₃ := MorphismRings.component p k n u v f₁ f₂ hp₁ hp₂ sq U.unop
  exact (congrArg (fun m => m ≫ (PrincipalComplex.Comparison.iso p k n X₁ Y₁ f₁ hp₁).hom.app
    (Opposite.op U.unop.val.1)) h₁).trans
      (h₂.trans (congrArg (fun m => (PrincipalComplex.Comparison.iso p k n X₂ Y₂ f₂ hp₂).hom.app
        (Opposite.op U.unop.val.2) ≫ (OrdinaryDeRhamFunctor.Ordinary.functor W).map m) h₃.symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismPrincipal.Comparison
