import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.Intersections
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.AdmissiblePreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.Schedule
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ExtractionOrder

/-! # Intersection Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Intrinsic boundary-intersection centers are compatible with all actual labelled boundaries. -/

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem Boundary.IntersectionCenters.Construction.boundaryIntersectionIdeal_map {R A : Type u} [CommRing R] [CommRing A]
    {ι : Type v} (w : ι → R) (C : Finset ι) (f : R →+* A) :
    (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C).map f = Boundary.CountReduction.Construction.boundaryIntersectionIdeal (fun j => f (w j)) C := by
  rw [Boundary.CountReduction.Construction.boundaryIntersectionIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

theorem Boundary.IntersectionCenters.Construction.boundaryIntersectionIdeal_mul_units {R : Type u} [CommRing R] {ι : Type v}
    (w : ι → R) (C : Finset ι) (v : ι → R) (hv : ∀ j, IsUnit (v j)) :
    Boundary.CountReduction.Construction.boundaryIntersectionIdeal (fun j => v j * w j) C = Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C :=
  BoundaryModel.Intersections.Construction.unit_mul_family_span (fun j : C => w j.val) (fun j : C => v j.val) (fun j => hv j.val)

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.intersection_center
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (C : Finset ι) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C) w C := by
  classical
  intro p hp
  obtain ⟨B⟩ := h p
  have hpoint : B.point.asIdeal.comap B.map.toRingHom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal B.point_over
  have hwp (j : C) : B.map (w j.val) ∈ B.point.asIdeal := by
    change w j.val ∈ B.point.asIdeal.comap B.map.toRingHom
    rw [hpoint]
    exact hp (Boundary.Schedule.Construction.boundaryIntersection_mem w C j.val j.property)
  have hex (j : C) : ∃ s, B.model.coordinate j.val = some s := by
    cases hj : B.model.coordinate j.val with
    | none =>
        have hu : IsUnit (B.map (w j.val)) := by
          rw [B.model.equation j.val, hj, mul_one]
          exact B.model.multiplierUnit j.val
        exact False.elim (B.point.asIdeal.notMem_of_isUnit hu (hwp j))
    | some s => exact ⟨s, rfl⟩
  choose s hs using hex
  let A : Finset B.model.indices := Finset.univ.image s
  have heq : (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C).map B.map.toRingHom =
      (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal A).map B.model.map := by
    rw [Boundary.IntersectionCenters.Construction.boundaryIntersectionIdeal_map, BoundaryModel.Intersections.Construction.coordinateIdeal_map_finite_family s B.model.map]
    change Ideal.span (Set.range (fun j : C => B.map (w j.val))) = _
    have hw : (fun j : C => B.map (w j.val)) =
        fun j : C => B.model.multiplier j.val * B.model.map (MvPolynomial.X (s j)) := by
      funext j
      simpa only [hs j] using B.model.equation j.val
    rw [hw]
    exact BoundaryModel.Intersections.Construction.unit_mul_family_span _ _ (fun j => B.model.multiplierUnit j.val)
  refine ⟨{ chart := B, coordinates := A, center_eq := heq, divided_iff := ?_ }⟩
  intro j
  constructor
  · intro hj
    exact ⟨s ⟨j, hj⟩, Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩, hs ⟨j, hj⟩⟩
  · rintro ⟨t, ht, hj⟩
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ht
    have he : j = l.val := B.model.distinct j l.val (s l) hj (hs l)
    exact he ▸ l.property

theorem Boundary.IntersectionCenters.Construction.boundary_monomial_intersection_permissible
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (w : ι → R) (a : ι → ℕ) (b : ℕ) (C : Finset ι)
    (hb : b ≤ ∑ j ∈ C, a j) :
    Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C ^ b := by
  classical
  let I := Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C
  have hC : (∏ j ∈ C, w j ^ a j) ∈ I ^ b :=
    Ideal.pow_le_pow_right hb
      (Boundary.ExtractionOrder.Construction.finite_boundary_product_mem_power C w a I (Boundary.Schedule.Construction.boundaryIntersection_mem w C))
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  have hprod : LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a =
      (∏ j ∈ C, w j ^ a j) * ∏ j ∈ Finset.univ \ C, w j ^ a j := by
    exact (Finset.prod_mul_prod_compl C (fun j => w j ^ a j)).symm
  rw [hprod]
  exact (I ^ b).mul_mem_right _ hC

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.blowup_intersection
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (C : Finset ι) (i : C) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C)
      (Boundary.Schedule.Construction.boundaryIntersectionGenerator w C i)))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C) (Boundary.Schedule.Construction.boundaryIntersectionGenerator w C i)
        C w (Boundary.Schedule.Construction.boundaryIntersection_mem w C)) := by
  exact MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup R (Boundary.CountReduction.Construction.boundaryIntersectionIdeal w C)
    w C (Boundary.Schedule.Construction.boundaryIntersection_mem w C) h (h.intersection_center C) (Boundary.Schedule.Construction.boundaryIntersectionGenerator w C i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
