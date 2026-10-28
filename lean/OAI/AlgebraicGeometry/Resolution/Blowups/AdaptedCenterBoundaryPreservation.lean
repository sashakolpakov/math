import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CenterCoordinateCompletion
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBoundaryPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange

/-! # Adapted Center Boundary Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedCenterBoundaryPreservation.Construction

noncomputable section

/-! Transfer exact local center-and-boundary coordinates to arbitrary actual blowup charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A local simultaneous coordinate chart through the image of a blowup
point supplies a genuine open normal-crossing chart through that point.
The new exceptional equation and all retained old equations are included. -/
theorem boundary_coordinate_center_blowup_open_chart
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R)
    {n : ℕ} (w : Fin n → R) (hw : ∀ j, w j ∈ I) (a : I)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (C : Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R I w
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) p) := by
  have het : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)) := inferInstance
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  obtain ⟨q, hq, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a C.map.toRingHom hf p C.point C.point_over
  let : Algebra (MvPolynomial C.indices k) C.carrier := C.coordinateMap.toAlgebra
  let : Algebra.Etale (MvPolynomial C.indices k) C.carrier :=
    RingHom.etale_algebraMap.mp C.coordinateEtale
  let : IsScalarTower k (MvPolynomial C.indices k) C.carrier :=
    IsScalarTower.of_algebraMap_eq (fun c => (C.coordinateGround c).symm)
  let a' : I.map C.map.toRingHom := ⟨C.map a.val, Ideal.mem_map_of_mem _ a.property⟩
  obtain ⟨D⟩ := Coordinate.CenterBoundaryPreservation.Construction.exists_boundary_blowup_open_chart_of_coordinates
    (I.map C.map.toRingHom) C.centerIndices C.centerIdeal
    C.boundaryIndex C.boundary_in_center (fun j => C.map (w j))
    (fun j => Ideal.mem_map_of_mem _ (hw j)) C.boundaryCoordinates a' q
  let f := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a C.map
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a C.map.toRingHom
  exact ⟨D.comp f (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw)
    (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional_map I a w hw C.map.toRingHom) p hq⟩

/-- Every point over a framed center has an actual normal-crossing open
chart after blowing up, for any included finite dual boundary frame and
any original denominator chart. -/
theorem exists_framed_center_boundary_blowup_open_chart
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (E : Fin n → Derivation k R R)
    (hE : ∀ i j, E i (w j) = if i = j then 1 else 0)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (a : Ideal.span (Set.range g))
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (Ideal.span (Set.range g)) a))
    (hp : Ideal.span (Set.range g) ≤
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants _ a) p).asIdeal) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart _ a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional _ a w hw) p) := by
  obtain ⟨C⟩ := Boundary.CenterCoordinateCompletion.Construction.exists_boundary_coordinate_center_open_chart k R g D hD w E hE hw
    (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants _ a) p) hp
  exact boundary_coordinate_center_blowup_open_chart k R _ w hw a p C

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedCenterBoundaryPreservation.Construction
