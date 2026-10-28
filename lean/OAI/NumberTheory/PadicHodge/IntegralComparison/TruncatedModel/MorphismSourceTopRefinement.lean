import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementAdditive
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTopRefinementData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdge

/-! # Morphism Source Top Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceTopRefinement

noncomputable section

/-! The original common-cover source edge agrees with the small-cover
native edge after the literal refinement of top-form Čech classes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  (g : ℕ) [SmoothOfRelativeDimension g X₁.hom] [SmoothOfRelativeDimension g X₂.hom]

variable
  {Y₁ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom]
  (f₁ : Y₁.left ⟶ X₁.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I₁ : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y₁) n))

omit [SmoothOfRelativeDimension g X₂.hom] in
theorem comparison (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X₁
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g) :
    MorphismTopEdge.sourceEdge p k n u f₁ hp₁ I₁ g (SourceTopRefinementData.Morphism.topMap p k n u g x) =
      IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X₁ Y₁ f₁ hp₁ I₁ (g+g)
        (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₁
          (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g x) := by
  have hc := MorphismSourceRefinementAdditive.comparison
    p k n u f₁ hp₁ I₁ (g+g)
    (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₁
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g x)
  have he := congrArg
    (MorphismGeometric.TruncatedModelMorphismGeometricAdditive.comparison p k n u f₁ hp₁ I₁ (g+g))
    (SourceTopRefinementData.Morphism.edge p k n u g x)
  exact he.symm.trans hc

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceTopRefinement
