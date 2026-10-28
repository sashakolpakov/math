import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarRangeCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IntegralCoordinates

/-! # Standard Padic Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.StandardPadicLattice.TestTransport

noncomputable section

/-! The literal standard p-adic lattice consists precisely of vectors
whose coordinates have norm at most one. -/

open scoped Classical

theorem standardPadicLattice_coordinates (q : ℕ) [Fact q.Prime]
    {J : Type*} [Fintype J] [DecidableEq J] (x : J → Padic q) :
    x ∈ Submodule.span (PadicInt q) (Set.range (fun j : J => (Pi.single j 1 : J → Padic q))) ↔
      ∀ j, ‖x j‖ ≤ 1 := by
  rw [ScalarRangeCoordinates.TestTransport.span_standard_vectors_iff]
  apply forall_congr'
  intro j
  constructor
  · rintro ⟨r, hr⟩
    exact hr ▸ r.property
  · intro hj
    exact ⟨⟨x j, hj⟩, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.StandardPadicLattice.TestTransport
