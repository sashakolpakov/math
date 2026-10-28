import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.LogarithmicCoordinates

/-! # Retraction Unit Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Compare actual boundary equations along maps agreeing on normalized coordinates. -/

universe u v

/-- Two maps agreeing on normalized equations differ on the original
unit-scaled equations by explicit invertible target factors. -/
theorem Boundary.RetractionUnitComparison.Construction.exists_unit_equation_comparison {R S : Type u} {ι : Type v}
    [CommRing R] [CommRing S] (g ρ : R →+* S) (w u z : ι → R)
    (hu : ∀ j, IsUnit (u j)) (hw : ∀ j, w j = u j * z j)
    (hz : ∀ j, g (z j) = ρ (z j)) :
    ∃ v : ι → S, (∀ j, IsUnit (v j)) ∧ ∀ j, g (w j) = v j * ρ (w j) := by
  let b (j : ι) := ((hu j).map ρ).unit
  let v (j : ι) := g (u j) * (↑((b j)⁻¹) : S)
  refine ⟨v, fun j => ((hu j).map g).mul ((b j)⁻¹).isUnit, ?_⟩
  intro j
  rw [hw j, map_mul, map_mul, hz j]
  change g (u j) * ρ (z j) = (g (u j) * ↑((b j)⁻¹)) * (ρ (u j) * ρ (z j))
  rw [← IsUnit.unit_spec ((hu j).map ρ)]
  change g (u j) * ρ (z j) = (g (u j) * ↑((b j)⁻¹)) * (↑(b j) * ρ (z j))
  symm
  calc
    _ = g (u j) * ((↑((b j)⁻¹) * ↑(b j)) * ρ (z j)) := by ring
    _ = g (u j) * ρ (z j) := by rw [Units.inv_mul, one_mul]

/-- Retaining all represented boundary coordinates retains the actual
original equations up to units, including any existing unit components. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.retraction_unit_comparison
    {k R S : Type u} {ι : Type v} [CommRing k] [CommRing R] [CommRing S] [Algebra k R]
    {w : ι → R} (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (g ρ : R →+* S)
    (h : ∀ s : M.boundaryIndices, g (M.map (MvPolynomial.X s.val)) = ρ (M.map (MvPolynomial.X s.val))) :
    ∃ v : ι → S, (∀ j, IsUnit (v j)) ∧ ∀ j, g (w j) = v j * ρ (w j) := by
  apply Boundary.RetractionUnitComparison.Construction.exists_unit_equation_comparison g ρ w M.multiplier M.coordinateEquation M.multiplierUnit
  · intro j
    rw [M.equation j]
    congr 1
    cases hc : M.coordinate j <;> simp only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hc]
  · intro j
    cases hc : M.coordinate j with
    | none => simp [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hc]
    | some s =>
        have hs : s ∈ M.boundaryIndices := (M.mem_boundaryIndices s).mpr ⟨j, hc⟩
        simpa only [Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateEquation, hc] using h ⟨s, hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
