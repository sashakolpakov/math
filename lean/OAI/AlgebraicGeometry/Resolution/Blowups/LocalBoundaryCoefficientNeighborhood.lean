import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCoefficientNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Local Boundary Coefficient Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryCoefficientNeighborhood.Construction

noncomputable section

/-! Boundary-compatible coefficient neighborhoods from the local normal-crossing property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- At every prime of maximum controlled order, the local boundary
property and the relative logarithmic bound supply an actual pointed
coefficient neighborhood with the full original boundary retained. -/
theorem exists_local_boundary_coefficient_open_chart
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] (w : ι → R) (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (J : Ideal R) (n : ℕ) (p : PrimeSpectrum R)
    (hJ : J.map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (n + 1))
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤) :
    Nonempty (Boundary.CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) := by
  obtain ⟨C⟩ := hboundary p
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)))
  let : Algebra R C.carrier := C.map.toRingHom.toAlgebra
  let : IsScalarTower k R C.carrier :=
    IsScalarTower.of_algebraMap_eq (fun c => (C.map.commutes c).symm)
  let : Algebra.Etale R C.carrier := RingHom.etale_algebraMap.mp hf
  have hlog : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k (fun j => C.map (w j))
      (J.map C.map.toRingHom) (n + 1) = ⊤ :=
    Relative.LogarithmicBoundary.Construction.relative_logarithmic_order_bound_map (S := C.carrier) k w J (n + 1) hbound
  have hp : C.point.asIdeal.comap C.map.toRingHom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  have horder : (J.map C.map.toRingHom).map
      (algebraMap C.carrier (Localization.AtPrime C.point.asIdeal)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime C.point.asIdeal) ^ (n + 1) :=
    (Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff C.map.toRingHom hf J p.asIdeal C.point.asIdeal hp.symm (n + 1)).mpr hJ
  obtain ⟨D⟩ := Modeled.BoundaryCoefficientNeighborhood.Construction.exists_modeled_boundary_coefficient_open_chart C.carrier
    (fun j => C.map (w j)) C.model (J.map C.map.toRingHom) n C.point horder hlog
  exact ⟨D.comp w J n C.map p C.point_over⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryCoefficientNeighborhood.Construction
