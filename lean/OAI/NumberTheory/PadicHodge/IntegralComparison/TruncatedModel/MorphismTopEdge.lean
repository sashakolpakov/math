import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismGeometricAdditive
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase

/-! # Morphism Top Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdge

noncomputable section

/-! Actual top-form pullback and the original bounded crystalline
pullback agree through the genuine common-cover top edges. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))
  (I₂ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₂) n))
  (g : ℕ) [SmoothOfRelativeDimension g X₁.hom] [SmoothOfRelativeDimension g X₂.hom]

def sourceEdge : MorphismTopEdgeBase.SourceTopForms p k n u g →+
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₁) n (g + g) :=
  (MorphismGeometric.TruncatedModelMorphismGeometricAdditive.comparison p k n u f₁ hp₁ I₁ (g + g)).comp
    (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₁ (MorphismTopEdgeBase.sourceCover p k n u) g).toAddMonoidHom

def targetEdge : MorphismTopEdgeBase.TargetTopForms p k n (X₂ := X₂) g →+
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (Witt.Crystalline.wittStructureMap p k Y₂) n (g + g) :=
  (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X₂ Y₂ f₂ hp₂ I₂ (g + g)).toAddMonoidHom.comp
    (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₂ (MorphismTopEdgeBase.targetCover p k n (X₂ := X₂)) g).toAddMonoidHom

include sq in
theorem square (x : MorphismTopEdgeBase.TargetTopForms p k n (X₂ := X₂) g) :
    BoundedCrystalline.CrystallinePullback.pullback v.left
      (MorphismData.Frames.ambient_over p k v) n (g + g)
      (targetEdge p k n f₂ hp₂ I₂ g x) =
    sourceEdge p k n u f₁ hp₁ I₁ g (MorphismTopEdgeBase.pullback p k n u g x) := by
  have h := MorphismGeometricAdditive.naturality
    p k n u v f₁ f₂ hp₁ hp₂ sq I₁ I₂ (g + g)
    (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₂ (MorphismTopEdgeBase.targetCover p k n (X₂ := X₂)) g x)
  have he := IntrinsicDeRham.TopEdgeMap.Intrinsic.naturality (Truncated.Witt.Ring p k n) X₁ X₂
    (MorphismTopEdgeBase.sourceCover p k n u) (MorphismTopEdgeBase.targetCover p k n (X₂ := X₂)) g (MorphismTopEdgeBase.bicomplexMap p k n u) x
  exact h.symm.trans (congrArg
    (MorphismGeometric.TruncatedModelMorphismGeometricAdditive.comparison p k n u f₁ hp₁ I₁ (g + g)) he)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdge
