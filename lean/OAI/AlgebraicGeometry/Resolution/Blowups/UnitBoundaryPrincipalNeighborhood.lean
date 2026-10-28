import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Operations
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Unit Boundary Principal Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryPrincipalNeighborhood.Construction

noncomputable section

/-! All absent finite boundary equations become units on one actual principal open. -/

theorem exists_unit_boundary_principal_neighborhood
    {R ι : Type*} [CommRing R] [Fintype ι] (w : ι → R)
    (p : PrimeSpectrum R) (hw : ∀ j, w j ∉ p.asIdeal) :
    ∃ f ∉ p.asIdeal, ∀ j, IsUnit (algebraMap R (Localization.Away f) (w j)) := by
  let f := ∏ j, w j
  have hf : f ∉ p.asIdeal := by
    exact p.asIdeal.primeCompl.prod_mem (fun j _ => hw j)
  have hu : IsUnit (∏ j, algebraMap R (Localization.Away f) (w j)) := by
    rw [← map_prod]
    exact IsLocalization.Away.algebraMap_isUnit f
  exact ⟨f, hf, IsUnit.prod_univ_iff.mp hu⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.UnitBoundaryPrincipalNeighborhood.Construction
