import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.BoundaryBlowupEveryPoint

/-! # Framed Ideal Boundary Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.FramedIdealBoundaryPreservation.Construction

noncomputable section

/-! Apply the boundary theorem to an actual named center ideal and its displayed frame. -/

universe u v

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_framed_ideal_boundary_blowup_open_chart
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R] (I : Ideal R)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range g) = I)
    {θ : Type v} [Fintype θ] (w : θ → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R θ w)
    (hw : ∀ j, w j ∈ I) (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a)) :
    Nonempty (Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) p) := by
  subst I
  exact Finite.BoundaryBlowupEveryPoint.Construction.exists_finite_boundary_blowup_open_chart_every_point k R g D hD w M hw a p

end

end OAI.AlgebraicGeometry.Resolution.Blowups.FramedIdealBoundaryPreservation.Construction
