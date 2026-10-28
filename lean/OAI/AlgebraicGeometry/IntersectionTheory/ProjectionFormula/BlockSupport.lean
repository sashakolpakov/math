import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointCongruence

/-! # Block Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockSupport

noncomputable section

/-! Native reduced-support projections in either disjoint block
agree with the finite source projection and the auxiliary projective
isomorphism at their corresponding points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)

theorem source_point
    (hS : ∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal)
    (W : IrreducibleCloseds (Projective.BlockSupports.ambient X m).carrier)
    (hW : Projection.PointCongruence.SupportData.NoBase (Projective.BlockSupports.ambient X m) m L W)
    (x : X.carrier) (hx : (Projective.BlockSupports.source X m).left x ∈ (W : Set (Projective.BlockSupports.ambient X m).carrier)) :
    Projection.PointCongruence.SupportData.projection (Projective.BlockSupports.ambient X m) m L W hW
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W ((Projective.BlockSupports.source X m).left x) hx) = BlockData.Projection.sourceProjection X m L hS x := by
  have hi : ∀ y, ((Projective.BlockSupports.source X m).left ≫ (Projective.BlockSupports.ambient X m).embedding) y ∈
      Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) := BlockData.Projection.source_domain X m L hS
  have h₁ := Projection.PointCongruence.support_point (Projective.BlockSupports.ambient X m) m L W hW (Projective.BlockSupports.source X m).left hi x hx
  have h₂ := Projection.PointCongruence.point (Projective.ConeSupport.coordinates L)
    (HomogeneousCoordinateMap.ofForms_C _ _)
    ((Projective.BlockSupports.source X m).left ≫ (Projective.BlockSupports.ambient X m).embedding)
    (X.embedding ≫ DisjointProjectiveBlocks.left X.ambientDimension m) hi (BlockData.Projection.source_domain X m L hS) x x rfl
  have h₃ := CoordinateBlock.Projection.point (DisjointProjectiveBlocks.leftIndex X.ambientDimension m)
    (DisjointProjectiveBlocks.left_injective X.ambientDimension m) L X.embedding
    (BlockData.Projection.source_domain X m L hS)
    (Projection.FiniteProjective.FromForms.in_domain X m (BlockData.Projection.sourceForms X m L) (BlockData.Projection.source_no_base X m L hS)) x
  exact h₁.trans (h₂.trans h₃)

theorem target_point
    (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
      ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)
    (W : IrreducibleCloseds (Projective.BlockSupports.ambient X m).carrier)
    (hW : Projection.PointCongruence.SupportData.NoBase (Projective.BlockSupports.ambient X m) m L W)
    (x : (Projective.Dimension.SpacePresentation.presentation m).carrier)
    (hx : (Projective.BlockSupports.target X m).left x ∈ (W : Set (Projective.BlockSupports.ambient X m).carrier)) :
    Projection.PointCongruence.SupportData.projection (Projective.BlockSupports.ambient X m) m L W hW
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W ((Projective.BlockSupports.target X m).left x) hx) = BlockData.Projection.targetProjection X m L hT x := by
  have hi : ∀ y, ((Projective.BlockSupports.target X m).left ≫ (Projective.BlockSupports.ambient X m).embedding) y ∈
      Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) := BlockData.Projection.target_domain X m L hT
  have h₁ := Projection.PointCongruence.support_point (Projective.BlockSupports.ambient X m) m L W hW (Projective.BlockSupports.target X m).left hi x hx
  have h₂ := Projection.PointCongruence.point (Projective.ConeSupport.coordinates L)
    (HomogeneousCoordinateMap.ofForms_C _ _)
    ((Projective.BlockSupports.target X m).left ≫ (Projective.BlockSupports.ambient X m).embedding)
    (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) ≫ DisjointProjectiveBlocks.right X.ambientDimension m) hi (BlockData.Projection.target_domain X m L hT) x x rfl
  have h₃ := CoordinateBlock.Projection.point (DisjointProjectiveBlocks.rightIndex X.ambientDimension m)
    (DisjointProjectiveBlocks.right_injective X.ambientDimension m) L (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace m))
    (BlockData.Projection.target_domain X m L hT)
    (Projection.FiniteProjective.FromForms.in_domain (Projective.Dimension.SpacePresentation.presentation m) m
      (BlockData.Projection.targetForms X m L) (BlockData.Projection.target_no_base X m L hT)) x
  exact h₁.trans (h₂.trans h₃)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockSupport
