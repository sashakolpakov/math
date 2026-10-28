import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.ResidualCoordinates
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualIntersection

/-! # Residual Coordinate Step -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualCoordinateStep

noncomputable section

/-! Explicit independent projection coordinates improve residual
intersections and are etale at a chosen closed point of the original support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : IrreducibleCloseds X.carrier) (hW : 1 ≤ X.supportCodimension W)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) (k : τ → ℕ)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ ResidualIntersection.Step.intersection X W (Z t) → k t ≤ X.supportCodimension C) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ y : X.carrier, ∃ a, (L a).val ∉ (X.embedding y).asHomogeneousIdeal),
      LinearIndependent ℂ L ∧
      (∃ x ∈ W, IsClosed {x} ∧
        (∃ U : X.carrier.Opens, x ∈ U ∧ Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)) ∧
        x ∉ ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) W) ∧
      ∀ t, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆
          (ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) W : Set X.carrier) ∩ (Z t : Set X.carrier) →
        min (X.supportCodimension W + X.supportCodimension (Z t)) (k t + 1) ≤ X.supportCodimension C := by
  classical
  let : JacobsonSpace X.carrier := LocallyOfFiniteType.jacobsonSpace X.structureMap
  have hwitness : ∀ D : IrreducibleCloseds X.carrier, ∃ x ∈ D, IsClosed {x} := by
    intro D
    obtain ⟨x, hxD, hxc⟩ := nonempty_inter_closedPoints D.isIrreducible.nonempty D.isClosed.isLocallyClosed
    exact ⟨x, hxD, hxc⟩
  choose point hpoint hclosed using hwitness
  let S t := ResidualIntersection.Step.intersection X W (Z t)
  let (t : τ) : NoetherianSpace (S t) := NoetherianSpace.set (S t : Set X.carrier)
  let (t : τ) : Finite (irreducibleComponents (S t)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S t)).to_subtype
  let J := Unit ⊕ (Σ t : τ, irreducibleComponents (S t))
  let T : J → IrreducibleCloseds X.carrier :=
    Sum.elim (fun _ => W) (fun j => CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j.1) j.2)
  obtain ⟨L, h, hLI, hpoints, hI⟩ := Generic.ResidualCoordinates.exists_coordinates X m
    (fun _ : τ => W) Z (fun _ : J => W) (fun _ => hW) (fun j => point (T j)) (fun j => hclosed (T j))
  let π := Projection.ProjectionCoincidence.over X m L h
  let : IsFinite π.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  refine ⟨L, h, hLI, ⟨point W, hpoint W, hclosed W, (hpoints (Sum.inl ())).1, (hpoints (Sum.inl ())).2⟩, ?_⟩
  intro t C hC
  apply ResidualIntersection.Criterion.bound X m π W (Z t) (k t) (hbound t) (hI t) _ C hC
  intro D
  exact ⟨point (T (Sum.inr ⟨t, D⟩)), hpoint (T (Sum.inr ⟨t, D⟩)), (hpoints (Sum.inr ⟨t, D⟩)).2⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualCoordinateStep
