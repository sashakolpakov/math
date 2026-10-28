import OAI.AlgebraicGeometry.Resolution.Blowups.FlatQuotientRegularity
import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedBoundaryFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts

/-! # Center Incidence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary incidence is detected by actual vanishing on a nonempty coordinate center. -/

open _root_.MvPolynomial

universe u v

theorem Boundary.CenterIncidence.Construction.subsetCoordinateCenter_outside_regular
    {k σ : Type u} [CommRing k] [IsDomain k] [DecidableEq σ]
    (C : Finset σ) (j : σ) (hj : j ∉ C) :
    IsRegular (Ideal.Quotient.mk (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C) (X j)) := by
  let e := Smooth.SubsetCenter.Construction.subsetCoordinateCenterAlgEquiv (R := k) C
  have h := TransformRegularElements.Construction.etale_ringHom_preserves_regular e.symm.toRingEquiv.toRingHom
    (RingHom.Etale.of_bijective e.symm.bijective) (X ⟨j, hj⟩) (IsRegular.of_ne_zero (X_ne_zero _))
  change IsRegular (Smooth.SubsetCenter.Construction.polynomialToSubsetCenter (R := k) C (X ⟨j, hj⟩)) at h
  rw [Smooth.SubsetCenter.Construction.polynomialToSubsetCenter_X] at h
  exact h

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.transverse_regular_mod_center
    {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R] {w : ι → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s) (j : ι) (hj : j ∉ F) :
    IsRegular (Ideal.Quotient.mk ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) (w j)) := by
  cases hcoord : M.coordinate j with
  | none =>
      have hu : IsUnit (w j) := by
        rw [M.equation j, hcoord, mul_one]
        exact M.multiplierUnit j
      exact (hu.map (Ideal.Quotient.mk _)).isRegular
  | some s =>
      have hs : s ∉ C := fun hs => hj ((hF j).mpr ⟨s, hs, hcoord⟩)
      let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
      let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
      have hr := FlatQuotientRegularity.Construction.flat_extended_quotient_regular (S := R) (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := k) C) (X s)
        (Boundary.CenterIncidence.Construction.subsetCoordinateCenter_outside_regular C s hs)
      rw [M.equation j, hcoord, map_mul]
      exact ((M.multiplierUnit j).map (Ideal.Quotient.mk _)).isRegular.mul hr

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.mem_coordinate_center_iff_divided
    {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R] {w : ι → R}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (hproper : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map ≠ ⊤) (j : ι) :
    w j ∈ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map ↔ j ∈ F := by
  constructor
  · intro hw
    by_contra hj
    let K := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map
    have hr := M.transverse_regular_mod_center C F hF j hj
    have hz : Ideal.Quotient.mk K (w j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hw
    have hone : Ideal.Quotient.mk K (1 : R) = 0 := by
      change (1 : R ⧸ K) = 0
      apply hr.left
      change Ideal.Quotient.mk K (w j) * 1 = Ideal.Quotient.mk K (w j) * 0
      rw [hz, zero_mul, zero_mul]
    exact hproper ((Ideal.eq_top_iff_one K).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hone))
  · exact M.coordinateCenter_boundary_mem C F hF j

theorem MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.divided_iff_mem
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) {ι : Type v} {w : ι → R} {F : Finset ι} {p : PrimeSpectrum R}
    (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p) (hp : I ≤ p.asIdeal) (j : ι) :
    j ∈ F ↔ C.chart.map (w j) ∈ I.map C.chart.map.toRingHom := by
  have hle : I.map C.chart.map.toRingHom ≤ C.chart.point.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    have he := congrArg PrimeSpectrum.asIdeal C.chart.point_over
    change C.chart.point.asIdeal.comap C.chart.map.toRingHom = p.asIdeal at he
    rw [he]
    exact hp
  have hproper : I.map C.chart.map.toRingHom ≠ ⊤ := by
    intro h
    exact C.chart.point.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
  rw [C.center_eq] at hproper ⊢
  exact (C.chart.model.mem_coordinate_center_iff_divided C.coordinates F C.divided_iff hproper j).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups
