import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction

/-! # Intersections -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Smooth actual intersections of every finite selection in an explicit boundary model. -/

universe u v

theorem BoundaryModel.Intersections.Construction.unit_mul_family_span {A : Type u} {ι : Type v} [CommRing A]
    (z u : ι → A) (hu : ∀ j, IsUnit (u j)) :
    Ideal.span (Set.range (fun j => u j * z j)) = Ideal.span (Set.range z) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply (Ideal.unit_mul_mem_iff_mem _ (hu j)).mp
    exact Ideal.subset_span ⟨j, rfl⟩

theorem BoundaryModel.Intersections.Construction.coordinateIdeal_map_finite_family {σ k A : Type u} {ι : Type v}
    [CommRing k] [CommRing A] [Fintype ι] [DecidableEq σ]
    (s : ι → σ) (φ : MvPolynomial σ k →+* A) :
    (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (Finset.univ.image s)).map φ =
      Ideal.span (Set.range (fun j => φ (MvPolynomial.X (s j)))) := by
  rw [SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨MvPolynomial.X (s j),
      ⟨s j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, rfl⟩, rfl⟩

variable {k A : Type u} {ι : Type v} [CommRing k] [CommRing A] [Algebra k A]
  {w : ι → A}

/-- Every finite boundary intersection in the explicit local model is
smooth over the original ground ring, including empty intersections. -/
theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.intersection_smooth (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w)
    (B : Finset ι) : Algebra.Smooth k (A ⧸ Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B) := by
  classical
  let : Algebra (MvPolynomial M.indices k) A := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) A := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  by_cases hnone : ∃ j ∈ B, M.coordinate j = none
  · obtain ⟨j, hj, hcoord⟩ := hnone
    have he : w j = M.multiplier j := by rw [M.equation j, hcoord, mul_one]
    have hu : IsUnit (w j) := by
      rw [he]
      exact M.multiplierUnit j
    have ht : Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩) hu
    rw [ht]
    infer_instance
  · have hex : ∀ j : B, ∃ s, M.coordinate j.val = some s := by
      intro j
      cases h : M.coordinate j.val with
      | none => exact False.elim (hnone ⟨j.val, j.property, h⟩)
      | some s => exact ⟨s, rfl⟩
    choose s hs using hex
    have hf : (fun j : B => w j.val) =
        (fun j : B => M.multiplier j.val * M.map (MvPolynomial.X (s j))) := by
      funext j
      simpa only [hs j] using M.equation j.val
    have hI : Boundary.CountReduction.Construction.boundaryIntersectionIdeal w B =
        (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (Finset.univ.image s)).map M.map := by
      rw [BoundaryModel.Intersections.Construction.coordinateIdeal_map_finite_family s M.map, Boundary.CountReduction.Construction.boundaryIntersectionIdeal, hf]
      exact BoundaryModel.Intersections.Construction.unit_mul_family_span _ _ (fun j => M.multiplierUnit j.val)
    rw [hI]
    exact Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateCenter_smooth (R := k) (S := A) (Finset.univ.image s)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
