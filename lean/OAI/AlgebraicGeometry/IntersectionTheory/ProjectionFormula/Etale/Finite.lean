import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.StalkUnramified
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.EqualDimensionEtale
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension

/-! # Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Finite.Projection

noncomputable section

/-! The finite projection can be chosen formally etale on the
actual stalks at every point of a prescribed finite set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_closed_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, (π.stalkMap (x j)).hom.FormallyEtale := by
  obtain ⟨π, hover, hfinite, hπ⟩ := Projection.StalkUnramified.Finite.exists_closed_points X m x hx
  refine ⟨π, hover, hfinite, fun j => ?_⟩
  let := Projective.Dimension.projective_relativeDimension m
  exact Smooth.EqualDimensionEtale.stalk π X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) hover m (x j) (hπ j)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Finite.Projection
