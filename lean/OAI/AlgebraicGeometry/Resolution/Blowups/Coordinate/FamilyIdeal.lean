import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup

/-! # Family Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FamilyIdeal.Construction

/-! Transporting selected function ideals to actual coordinate centers. -/

universe u

variable {A L k ι : Type u} {ν : Type} [CommRing A] [CommRing L] [CommRing k]
  [DecidableEq ι] [DecidableEq ν]

def coordinateFamilyIdeal (z : ι → A) (C : Finset ι) : Ideal A :=
  Ideal.span (z '' (C : Set ι))

/-- An adapted coordinate map transports the ideal of any selected
subfamily to the corresponding coordinate-subset ideal. -/
theorem coordinateFamilyIdeal_map_eq_coordinate_center (z : ι → A) (C : Finset ι)
    (ρ : A →+* L) (φ : MvPolynomial (ν ⊕ ι) k →+* L)
    (hz : ∀ j, φ (MvPolynomial.X (Sum.inr j)) = ρ (z j)) :
    (coordinateFamilyIdeal z C).map ρ =
      (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) (C.image (Sum.inr : ι → ν ⊕ ι))).map φ := by
  rw [coordinateFamilyIdeal, SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span, Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨a, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨MvPolynomial.X (Sum.inr j), ?_, hz j⟩
    exact ⟨Sum.inr j, Finset.mem_image_of_mem Sum.inr hj, rfl⟩
  · rintro ⟨a, ⟨ij, hij, rfl⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hij
    exact ⟨z j, ⟨j, hj, rfl⟩, (hz j).symm⟩

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.FamilyIdeal.Construction
