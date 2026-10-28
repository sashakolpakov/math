import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSourceRefinementCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismTopEdgeBase

/-! # Source Top Refinement Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTopRefinementData.Morphism

noncomputable section

/-! Literal refinement of native top-form classes and its original top-edge square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated] (u : X₁ ⟶ X₂)
  (g : ℕ) [SmoothOfRelativeDimension g X₁.hom] [SmoothOfRelativeDimension g X₂.hom]

def topMap :
    IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X₁
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g →ₗ[Truncated.Witt.Ring p k n]
    MorphismTopEdgeBase.SourceTopForms p k n u g :=
  (homologyMap
    (ModuleCech.CoverRefinement.map (Truncated.Witt.Ring p k n) X₁
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁)
      (MorphismTopEdgeBase.sourceCover p k n u)
      (MorphismSourceRefinementCoordinates.openRefinement p k n u)
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X₁ g)) g).hom

omit [Fintype k] [CharP k p] [X₁.left.IsSeparated] [X₂.left.IsSeparated] [SmoothOfRelativeDimension g X₂.hom] in
theorem edge (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X₁
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g) :
    homologyMap (MorphismSourceRefinementCoordinates.map p k n u) (g+g)
      (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₁
        (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁) g x) =
    IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X₁
      (MorphismTopEdgeBase.sourceCover p k n u) g (topMap p k n u g x) :=
  IntrinsicDeRham.CoverRefinement.Intrinsic.top_edge (Truncated.Witt.Ring p k n) X₁
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X₁)
    (MorphismTopEdgeBase.sourceCover p k n u)
    (MorphismSourceRefinementCoordinates.openRefinement p k n u) g x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SourceTopRefinementData.Morphism
