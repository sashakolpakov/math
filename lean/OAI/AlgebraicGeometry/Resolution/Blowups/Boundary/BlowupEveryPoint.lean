import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryBlowupPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OutsideCenter

/-! # Blowup Every Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupEveryPoint.Construction

noncomputable section

/-! Boundary preservation at all primes of every actual framed-center blowup chart. -/

universe u

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- If a framed center lies in every selected boundary component, every
prime of every actual blowup chart admits an étale normal-crossing model
for the new exceptional equation and the divided old equations. -/
theorem exists_boundary_blowup_open_chart_every_point
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Fin n) w)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (a : Ideal.span (Set.range g))
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) a)) :
    Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw) p) := by
  by_cases hp : Ideal.span (Set.range g) ≤
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants _ a) p).asIdeal
  · exact Modeled.BoundaryBlowupPreservation.Construction.exists_modeled_boundary_blowup_open_chart k R g D hD w M hw a p hp
  · exact OutsideCenter.Construction.exists_boundary_blowup_open_chart_outside_center k R w M _ a hw p hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.BlowupEveryPoint.Construction
