import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.LocalComponentFactors
import OAI.AlgebraicGeometry.Resolution.Blowups.LabelledBoundaryMonomialTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty
import OAI.AlgebraicGeometry.Resolution.Blowups.PointOverClosedPoint

/-! # Monomial Exponent Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A nonunit boundary component has precisely its displayed monomial exponent. -/

universe u v

theorem Boundary.MonomialExponentBound.Construction.boundaryMonomial_power_bound
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (w : ι → R) (a : ι → ℕ) (j : ι) (hreg : IsRegular (w j))
    (hprime : (Ideal.span {w j}).IsPrime) (hind : ∀ i, i ≠ j → w i ∉ Ideal.span {w j})
    (b : ℕ) (hbound : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ Ideal.span {w j} ^ b) : b ≤ a j := by
  have htop : ¬ (⊤ : Ideal R) ≤ Ideal.span {w j} := fun h => hprime.ne_top (top_le_iff.mp h)
  have h := Boundary.FactorUniqueness.Construction.finite_prime_boundary_factor_exact_exponent Finset.univ w a ⊤ j (Finset.mem_univ j)
    hreg hprime (fun i _ hi => hind i hi) htop
  rw [Ideal.mul_top] at h
  by_contra hb
  apply h.2
  exact hbound.trans (Ideal.pow_le_pow_right (by omega))

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.monomial_exponent_bound_or_unit
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {w : ι → R} (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : ι → ℕ) (j : ι) (b : ℕ)
    (hbound : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ Ideal.span {w j} ^ b) :
    b ≤ a j ∨ IsUnit (w j) := by
  classical
  by_cases hu : IsUnit (w j)
  · exact Or.inr hu
  · have hproper : Ideal.span {w j} ≠ (⊤ : Ideal R) := fun h => hu (Ideal.span_singleton_eq_top.mp h)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {w j}) hproper
    let : P.IsMaximal := hP
    let p : PrimeSpectrum R := ⟨P, inferInstance⟩
    have hwP : w j ∈ P := hle (Ideal.mem_span_singleton_self (w j))
    obtain ⟨C⟩ := hboundary p
    obtain ⟨Q, hQ, hQP⟩ := PointOverClosedPoint.Construction.exists_maximal_point_over_closed_point C.map.toRingHom P C.point
      (congrArg PrimeSpectrum.asIdeal C.point_over)
    let : Q.IsMaximal := hQ
    have hwQ : C.map (w j) ∈ Q := by
      change w j ∈ Q.comap C.map.toRingHom
      rwa [hQP]
    let A := Localization.AtPrime Q
    let φ : R →+* A := (algebraMap C.carrier A).comp C.map.toRingHom
    obtain ⟨hreg, hprime, hind⟩ := C.model.local_component_factor_properties Q j hwQ
    have hmap := Ideal.map_mono (f := φ) hbound
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hmap
    have he : φ (LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a) = LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (fun i => φ (w i)) a := by
      simp only [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, map_prod, map_pow]
    rw [he] at hmap
    exact Or.inl (Boundary.MonomialExponentBound.Construction.boundaryMonomial_power_bound (fun i => φ (w i)) a j hreg hprime hind b hmap)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
