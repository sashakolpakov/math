import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Finite
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.StalkNeighborhood

/-! # Etale Neighborhoods -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleNeighborhoods

noncomputable section

/-! Every finite family of closed points admits one finite linear
projection that is etale on an open neighborhood of each selected point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, ∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ π) := by
  obtain ⟨π, hover, hfinite, hπ⟩ := ProjectionFormula.Etale.Finite.Projection.exists_closed_points X m x hx
  let := hfinite
  refine ⟨π, hover, hfinite, fun j => ?_⟩
  exact ProjectionFormula.Etale.StalkNeighborhood.exists_open π (x j) (hπ j)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleNeighborhoods
