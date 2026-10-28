import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointBlockForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlock
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SquareIso

/-! # Block Data -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData

noncomputable section

/-! The projection on the source block is finite, and its restriction
to the auxiliary square block is an isomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)

def sourceForms : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 :=
  fun a => CoordinateBlockForms.restrict (DisjointProjectiveBlocks.leftIndex X.ambientDimension m) (L a)

def targetForms : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 :=
  fun a => CoordinateBlockForms.restrict (DisjointProjectiveBlocks.rightIndex X.ambientDimension m) (L a)

variable (hS : ∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal)
  (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
    ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)

include hS in
theorem source_no_base (x : X.carrier) :
    ∃ a, (sourceForms X m L a).val ∉ (X.embedding x).asHomogeneousIdeal := by
  obtain ⟨a, ha⟩ := hS x
  exact ⟨a, ha⟩

include hT in
theorem target_no_base (x : (Projective.Dimension.SpacePresentation.presentation m).carrier) :
    ∃ a, (targetForms X m L a).val ∉ ((Projective.Dimension.SpacePresentation.presentation m).embedding x).asHomogeneousIdeal := by
  obtain ⟨a, ha⟩ := hT x
  exact ⟨a, ha⟩

def sourceProjection : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Projection.FiniteProjective.FromForms.map X m (sourceForms X m L) (source_no_base X m L hS)

def targetProjection : (Projective.Dimension.SpacePresentation.presentation m).carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Projection.FiniteProjective.FromForms.map (Projective.Dimension.SpacePresentation.presentation m) m (targetForms X m L) (target_no_base X m L hT)

instance source_finite : IsFinite (sourceProjection X m L hS) :=
  inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m (sourceForms X m L) (source_no_base X m L hS)))

instance target_finite : IsFinite (targetProjection X m L hT) :=
  inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map (Projective.Dimension.SpacePresentation.presentation m) m
    (targetForms X m L) (target_no_base X m L hT)))

theorem target_isIso (hLI : LinearIndependent ℂ (targetForms X m L)) : IsIso (targetProjection X m L hT) :=
  SquareIso.Projection.isIso (targetForms X m L) hLI
    (Projection.FiniteProjective.FromForms.in_domain (Projective.Dimension.SpacePresentation.presentation m) m
      (targetForms X m L) (target_no_base X m L hT))

theorem source_over : sourceProjection X m L hS ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap :=
  Projection.FiniteProjective.FromForms.over_base X m (sourceForms X m L) (source_no_base X m L hS)

theorem target_over : targetProjection X m L hT ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
    (Projective.Dimension.SpacePresentation.presentation m).structureMap :=
  Projection.FiniteProjective.FromForms.over_base (Projective.Dimension.SpacePresentation.presentation m) m
    (targetForms X m L) (target_no_base X m L hT)

include hS in
theorem source_domain (x : X.carrier) :
    (X.embedding ≫ DisjointProjectiveBlocks.left X.ambientDimension m) x ∈
      Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) :=
  (CoordinateBlock.Projection.mem_domain _ (DisjointProjectiveBlocks.left_injective _ _) L (X.embedding x)).mpr
    (Projection.FiniteProjective.FromForms.in_domain X m (sourceForms X m L) (source_no_base X m L hS) x)

include hT in
theorem target_domain (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) ≫ DisjointProjectiveBlocks.right X.ambientDimension m) x ∈
      Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L) :=
  (CoordinateBlock.Projection.mem_domain _ (DisjointProjectiveBlocks.right_injective _ _) L x).mpr
    (Projection.FiniteProjective.FromForms.in_domain (Projective.Dimension.SpacePresentation.presentation m) m
      (targetForms X m L) (target_no_base X m L hT) x)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData
