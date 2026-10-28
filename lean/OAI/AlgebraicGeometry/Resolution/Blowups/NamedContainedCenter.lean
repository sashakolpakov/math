import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.ContainedHypersurfaceCenter

/-! # Named Contained Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Preserve a named actual center ideal when adjoining a contained transverse hypersurface. -/

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.named_contained_hypersurface_center_chart
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (I : Ideal R) (C : Finset M.indices) (hI : I = (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map)
    (F : Finset ι) (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (p : PrimeSpectrum R) (hC : I ≤ p.asIdeal)
    (z : R) (hz : z ∈ I) (E : Derivation k R R)
    (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z ∉ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) p) := by
  subst I
  exact M.contained_hypersurface_center_chart C F hF p hC z hz E hE hEz

end

end OAI.AlgebraicGeometry.Resolution.Blowups
