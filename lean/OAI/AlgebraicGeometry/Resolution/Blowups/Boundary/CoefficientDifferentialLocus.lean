import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryCoefficientNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientOpenPoints
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport

/-! # Coefficient Differential Locus -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientDifferentialLocus.Construction

noncomputable section

/-! Coefficient charts cover the entire closed differential locus, including nonclosed primes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

/-- Choose maximal contact at a maximal specialization, then retain the
original prime on the same open. Membership in the differential locus
ensures that its lifted point remains on the normal hypersurface. -/
theorem exists_boundary_coefficient_chart_of_differential_locus
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type v} [Fintype ι] (w : ι → R) (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (J : Ideal R) (n : ℕ)
    (hbound : Relative.LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J (n + 1) = ⊤)
    (p : PrimeSpectrum R) (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ p.asIdeal) :
    Nonempty (CoefficientOpenChart.Construction.BoundaryCoefficientOpenChart k R w J n p) := by
  obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let : q.IsMaximal := hq
  have horder : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1) :=
    (Blowups.Smooth.ClosedPointChartTransport.Construction.smooth_closedPoint_order_iff_relative_differentialIdeal k J q n).mpr (hp.trans hpq)
  obtain ⟨C⟩ := LocalBoundaryCoefficientNeighborhood.Construction.exists_local_boundary_coefficient_open_chart R w hboundary J n
    (⟨q, inferInstance⟩ : PrimeSpectrum R) horder hbound
  have hmem : p ∈ C.openRange :=
    ((PrimeSpectrum.le_iff_specializes p ⟨q, inferInstance⟩).mp hpq).mem_open
      C.openRange.isOpen C.point_mem_openRange
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum C.carrier, PrimeSpectrum.comap C.map.toRingHom P = p := hmem
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)))
  have hz : C.normal ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map C.map.toRingHom := by
    rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k C.map hf J n]
    exact C.normal_mem
  have hPI : P.asIdeal.comap C.map.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hP
  have hle : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map C.map.toRingHom ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hPI]
    exact hp
  exact ⟨C.atPoint p P hP (hle hz)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoefficientDifferentialLocus.Construction
