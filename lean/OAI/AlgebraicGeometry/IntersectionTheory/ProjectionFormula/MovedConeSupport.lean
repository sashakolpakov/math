import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeCodimension

/-! # Moved Cone Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedConeSupport

noncomputable section

/-! The cone defined by the new source coordinates over the projected
auxiliary base has the original codimension and the expected inverse-image set. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BlockData.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1)
  (hS : ∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal)
  (hT : ∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
    ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal)

include hS in
theorem source_no_base (Z : IrreducibleCloseds X.carrier) :
    Projection.PointCongruence.SupportData.NoBase (Projective.BlockSupports.ambient X m) m L (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) Z) := by
  intro y hy
  rw [ProperCycleLinearity.imageSupport_eq_image] at hy
  obtain ⟨x, _, rfl⟩ := hy
  exact hS x

include hT in
theorem target_no_base (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier) :
    Projection.PointCongruence.SupportData.NoBase (Projective.BlockSupports.ambient X m) m L (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) := by
  intro y hy
  rw [ProperCycleLinearity.imageSupport_eq_image] at hy
  obtain ⟨x, _, rfl⟩ := hy
  exact hT x

variable (hLI : LinearIndependent ℂ (BlockData.Projection.sourceForms X m L))
  (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier)

def cone : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension) :=
  Projective.ConeSupport.support (BlockData.Projection.sourceForms X m L) hLI (BlockData.Projection.targetProjection X m L hT (CycleClass.Thom.IntersectionGeometry.supportPoint S))

theorem codimension :
    (Projective.Dimension.SpacePresentation.presentation X.ambientDimension).supportCodimension (cone X m L hT hLI S) =
      (Projective.Dimension.SpacePresentation.presentation m).supportCodimension S := by
  let σ : (Projective.Dimension.SpacePresentation.presentation m).toOver ⟶
      (Projective.Dimension.SpacePresentation.presentation m).toOver :=
    Over.homMk (BlockData.Projection.targetProjection X m L hT) (BlockData.Projection.target_over X m L hT)
  let : IsFinite σ.left := inferInstanceAs (IsFinite (BlockData.Projection.targetProjection X m L hT))
  exact (Projective.ConeCodimension.codimension (BlockData.Projection.sourceForms X m L) hLI
    (BlockData.Projection.targetProjection X m L hT (CycleClass.Thom.IntersectionGeometry.supportPoint S))).trans (Finite.Codimension.Projection.image σ m S)

theorem preimage : X.embedding ⁻¹' (cone X m L hT hLI S : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) =
    BlockData.Projection.sourceProjection X m L hS ⁻¹' (BlockData.Projection.targetProjection X m L hT '' (S : Set (Projective.Dimension.SpacePresentation.presentation m).carrier)) := by
  have he := Projective.ConePreimage.finite_image (BlockData.Projection.targetProjection X m L hT) S
  ext x
  have hm := Projective.ConePreimage.mem_iff (BlockData.Projection.sourceForms X m L) hLI
    (BlockData.Projection.targetProjection X m L hT (CycleClass.Thom.IntersectionGeometry.supportPoint S)) X.embedding
    (Projection.FiniteProjective.FromForms.in_domain X m (BlockData.Projection.sourceForms X m L) (BlockData.Projection.source_no_base X m L hS)) x
  exact hm.trans ((congrArg (fun A : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) => BlockData.Projection.sourceProjection X m L hS x ∈ A) he).to_iff)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedConeSupport
