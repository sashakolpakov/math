import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupEveryPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartRestriction

/-! # Boundary Blowup Every Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryBlowupEveryPoint.Construction

noncomputable section

/-! Retain arbitrary finite original boundary labels in every blowup chart. -/

universe u v

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The all-primes preservation theorem retains any finite original
label type; the temporary enumeration is undone on the resulting chart. -/
theorem exists_finite_boundary_blowup_open_chart_every_point
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {θ : Type v} [Fintype θ] (w : θ → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R θ w)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (a : Ideal.span (Set.range g))
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) a)) :
    Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw) p) := by
  classical
  let E := Fintype.equivFin θ
  obtain ⟨C⟩ := Boundary.BlowupEveryPoint.Construction.exists_boundary_blowup_open_chart_every_point k R g D hD
    (fun j => w (E.symm j)) (M.reindex E.symm.toEmbedding) (fun j => hw (E.symm j)) a p
  let e : Option θ ↪ Option (Fin (Fintype.card θ)) := E.toEmbedding.optionMap
  let B := C.reindex e
  have he : (fun j => Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a
      (fun l => w (E.symm l)) (fun l => hw (E.symm l)) (e j)) =
      Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw := by
    funext j
    cases j with
    | none => rfl
    | some j =>
        change ExceptionalIdeal.Construction.blowupChartRatio _ a ⟨w (E.symm (E j)), _⟩ = ExceptionalIdeal.Construction.blowupChartRatio _ a ⟨w j, hw j⟩
        apply congrArg (ExceptionalIdeal.Construction.blowupChartRatio _ a)
        exact Subtype.ext (congrArg w (E.symm_apply_apply j))
  change Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
    (fun j => Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a
      (fun l => w (E.symm l)) (fun l => hw (E.symm l)) (e j)) p at B
  rw [he] at B
  exact ⟨B⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryBlowupEveryPoint.Construction
