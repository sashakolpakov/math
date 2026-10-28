import OAI.AlgebraicGeometry.Resolution.Blowups.TransverseBoundaryFlatTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.FlatContainment

/-! # Transverse Regularity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Distinct normal-crossing boundary labels are regular modulo one another. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v

theorem Boundary.TransverseRegularity.Construction.map_colon_principal_le {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (c : R) (φ : R →+* S) :
    (I.colon (Ideal.span {c} : Set R)).map φ ≤
      (I.map φ).colon (Ideal.span {φ c} : Set S) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  apply Ideal.mem_colon_span_singleton.mpr
  rw [← map_mul]
  exact Ideal.mem_map_of_mem φ (Ideal.mem_colon_span_singleton.mp hx)

theorem Boundary.TransverseRegularity.Construction.ideal_colon_eq_of_pointed_flat_charts {R : Type u} [CommRing R]
    (I : Ideal R) (c : R)
    (h : ∀ p : PrimeSpectrum R, ∃ (S : CommRingCat.{u}) (φ : R →+* S), φ.Flat ∧
      ∃ q : PrimeSpectrum S, PrimeSpectrum.comap φ q = p ∧
        (I.map φ).colon (Ideal.span {φ c} : Set S) = I.map φ) :
    I.colon (Ideal.span {c} : Set R) = I := by
  apply le_antisymm ?_ Ideal.le_colon
  apply Pointed.FlatContainment.Construction.ideal_le_of_pointed_flat_charts
  intro p
  obtain ⟨S, φ, hφ, q, hq, hI⟩ := h p
  exact ⟨S, φ, hφ, q, hq, hI ▸ Boundary.TransverseRegularity.Construction.map_colon_principal_le I c φ⟩

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.distinct_component_colon
    {k A : Type u} {ι : Type v} [Field k] [CommRing A] [Algebra k A] {w : ι → A}
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k A ι w) (i j : ι) (hij : i ≠ j) :
    (Ideal.span {w i}).colon (Ideal.span {w j} : Set A) = Ideal.span {w i} := by
  rw [M.component_ideal i, M.component_ideal j]
  cases hi : M.coordinate i with
  | none => exact Submodule.top_colon
  | some s =>
      cases hj : M.coordinate j with
      | none =>
          ext x
          constructor
          · intro hx
            simpa only [smul_eq_mul, mul_one] using (Submodule.mem_colon.mp hx) 1 trivial
          · intro hx
            exact Ideal.le_colon hx
      | some t =>
          have hst : s ≠ t := by
            intro hst
            exact hij (M.distinct i j t (hst ▸ hi) hj)
          let : Algebra (MvPolynomial M.indices k) A := M.map.toAlgebra
          let : Algebra.Etale (MvPolynomial M.indices k) A := RingHom.etale_algebraMap.mp M.etale
          have h := FlatQuotientRegularity.Construction.flat_map_colon_self (S := A) (Ideal.span {(X s : MvPolynomial M.indices k)}) (X t)
            (TransverseCoordinateBoundaryTransform.Construction.coordinate_principal_colon_distinct t s hst)
          rw [Ideal.map_span, Set.image_singleton] at h
          change (Ideal.span {M.map (X s)}).colon (Ideal.span {M.map (X t)} : Set A) =
            Ideal.span {M.map (X s)} at h
          exact h

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.distinct_component_colon
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} {w : ι → R} (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (i j : ι) (hij : i ≠ j) :
    (Ideal.span {w i}).colon (Ideal.span {w j} : Set R) = Ideal.span {w i} := by
  apply Boundary.TransverseRegularity.Construction.ideal_colon_eq_of_pointed_flat_charts
  intro p
  obtain ⟨C⟩ := h p
  have hf : Flat (Spec.map (CommRingCat.ofHom C.map.toRingHom)) := inferInstance
  refine ⟨C.carrier, C.map.toRingHom,
    (HasRingHomProperty.Spec_iff (P := @Flat)).mp hf, C.point, C.point_over, ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  exact C.model.distinct_component_colon i j hij

end

end OAI.AlgebraicGeometry.Resolution.Blowups
