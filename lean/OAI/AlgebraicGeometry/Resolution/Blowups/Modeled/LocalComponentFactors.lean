import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryFactorUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BoundaryModel

/-! # Local Component Factors -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A local boundary component is regular and prime and divides no other actual labelled equation. -/

universe u v

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.local_component_factor_properties
    {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R]
    {ι : Type v} {w : ι → R} (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (q : Ideal R) [q.IsMaximal] (j : ι) (hj : w j ∈ q) :
    IsRegular (algebraMap R (Localization.AtPrime q) (w j)) ∧
      (Ideal.span {algebraMap R (Localization.AtPrime q) (w j)}).IsPrime ∧
      ∀ i, i ≠ j → algebraMap R (Localization.AtPrime q) (w i) ∉
        Ideal.span {algebraMap R (Localization.AtPrime q) (w j)} := by
  classical
  let A := Localization.AtPrime q
  let φ : R →+* A := algebraMap R A
  obtain ⟨s, hs⟩ : ∃ s, M.coordinate j = some s := by
    cases h : M.coordinate j with
    | none =>
        have hu : IsUnit (w j) := by
          rw [M.equation j, h, mul_one]
          exact M.multiplierUnit j
        exact False.elim (q.notMem_of_isUnit hu hj)
    | some s => exact ⟨s, rfl⟩
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (MvPolynomial M.indices k) R
  have hzq : M.map (MvPolynomial.X s) ∈ q := by
    apply (q.unit_mul_mem_iff_mem (M.multiplierUnit j)).mp
    simpa only [M.equation j, hs] using hj
  have hsingleton (i : M.indices) (hi : i ∈ ({s} : Finset M.indices)) :
      algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X i) ∈ q := by
    have hi' : i = s := Finset.mem_singleton.mp hi
    subst i
    exact hzq
  obtain ⟨hreg, hprime, _⟩ := Blowups.Etale.BoundaryFactorUniqueness.Construction.etale_local_boundary_factor_properties (K := k) (S := R) {s} q hsingleton
  have hscalar : φ (w j) = φ (M.multiplier j) * φ (M.map (MvPolynomial.X s)) := by
    rw [M.equation j, hs, map_mul]
  have heq : Ideal.span {φ (w j)} = Ideal.span {φ (M.map (MvPolynomial.X s))} := by
    rw [hscalar]
    exact Ideal.span_singleton_mul_left_unit ((M.multiplierUnit j).map φ) _
  have hprimej : (Ideal.span {φ (w j)}).IsPrime := by
    rw [heq]
    exact hprime s (Finset.mem_singleton_self s)
  refine ⟨?_, hprimej, ?_⟩
  · rw [hscalar]
    exact ((M.multiplierUnit j).map φ).isRegular.mul (hreg s (Finset.mem_singleton_self s))
  · intro i hij
    cases hi : M.coordinate i with
    | none =>
        have hui : IsUnit (w i) := by
          rw [M.equation i, hi, mul_one]
          exact M.multiplierUnit i
        let : (Ideal.span {φ (w j)}).IsPrime := hprimej
        exact (Ideal.span {φ (w j)}).notMem_of_isUnit (hui.map φ)
    | some t =>
        have hts : t ≠ s := by
          intro h
          apply hij
          exact M.distinct i j t hi (hs.trans (congrArg some h.symm))
        let : Algebra.FormallyEtale R A := Algebra.FormallyEtale.of_isLocalization q.primeCompl
        let D := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) t)
        have hDs : D (φ (M.map (MvPolynomial.X s))) = 0 := by
          change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) _
            (algebraMap R A (algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X s))) = 0
          rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X,
            ite_eq_right hts, map_zero]
        have hDt : D (φ (M.map (MvPolynomial.X t))) = 1 := by
          change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) _
            (algebraMap R A (algebraMap (MvPolynomial M.indices k) R (MvPolynomial.X t))) = 1
          rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X,
            ite_eq_left rfl, map_one]
        have hzmax : φ (M.map (MvPolynomial.X s)) ∈ IsLocalRing.maximalIdeal A := by
          change M.map (MvPolynomial.X s) ∈ (IsLocalRing.maximalIdeal A).under R
          rw [IsLocalization.AtPrime.under_maximalIdeal A q]
          exact hzq
        have hnot := Boundary.FactorUniqueness.Construction.transverse_coordinate_not_mem_span (k := k) D (φ (M.map (MvPolynomial.X s)))
          (φ (M.map (MvPolynomial.X t))) hDs hDt (IsLocalRing.maximalIdeal A)
          (IsLocalRing.maximalIdeal.isMaximal A).ne_top hzmax
        intro hwi
        apply hnot
        rw [heq] at hwi
        apply (Ideal.unit_mul_mem_iff_mem _ ((M.multiplierUnit i).map φ)).mp
        have hsi : φ (w i) = φ (M.multiplier i) * φ (M.map (MvPolynomial.X t)) := by
          rw [M.equation i, hi, map_mul]
        rwa [← hsi]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
