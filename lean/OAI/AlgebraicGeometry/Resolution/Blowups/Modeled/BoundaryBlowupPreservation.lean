import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCenterCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedCenterBoundaryPreservation

/-! # Boundary Blowup Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryBlowupPreservation.Construction

noncomputable section

/-! A boundary model can be reused at a later framed center containing its selected equations. -/

universe u

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- The actual boundary model is preserved over any subsequent framed
center inside every selected boundary component, on every denominator chart.
No exact global dual frame for the boundary equations is assumed. -/
theorem exists_modeled_boundary_blowup_open_chart
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Fin n) w)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (a : Ideal.span (Set.range g))
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) a))
    (hp : Ideal.span (Set.range g) ≤
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants _ a) p).asIdeal) :
    Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw) p) := by
  obtain ⟨C⟩ := BoundaryCenterCoordinates.Construction.exists_modeled_boundary_center_coordinates k R g D hD w M hw
    (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants _ a) p) hp
  exact AdaptedCenterBoundaryPreservation.Construction.boundary_coordinate_center_blowup_open_chart k R _ w hw a p C

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryBlowupPreservation.Construction
