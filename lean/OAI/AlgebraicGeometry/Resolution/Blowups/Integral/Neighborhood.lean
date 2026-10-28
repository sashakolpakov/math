import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalDomain
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainmentNeighborhood

/-! # Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.Neighborhood.Construction

noncomputable section

/-! Actual integral affine neighborhoods at points with domain local rings. -/

section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- A domain local ring on a Noetherian affine scheme has an actual
principal integral neighborhood. The localization kernel is finitely generated,
so it can be killed on one principal open containing the chosen point. -/
theorem exists_domain_principal_neighborhood (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] :
    ∃ f ∉ q, IsDomain (Localization.Away f) := by
  let T := Localization.AtPrime q
  let P := RingHom.ker (algebraMap R T)
  have hP : P.map (algebraMap R T) = (⊥ : Ideal R).map (algebraMap R T) := by
    rw [Ideal.map_bot]
    rw [Ideal.map_eq_bot_iff_le_ker]
  obtain ⟨f, hf, hmap⟩ := LocalContainmentNeighborhood.Construction.exists_neighborhood_ideal_equality P ⊥ q
    (IsNoetherian.noetherian P) (IsNoetherian.noetherian (⊥ : Ideal R)) hP
  let A := Localization.Away f
  have hunit : IsUnit (algebraMap R T f) := IsLocalization.map_units T (⟨f, hf⟩ : q.primeCompl)
  let φ : A →+* T := IsLocalization.Away.lift (g := algebraMap R T) f hunit
  have hφ : Function.Injective φ := by
    apply (RingHom.injective_iff_ker_eq_bot φ).mpr
    apply bot_unique
    intro x hx
    change φ x = 0 at hx
    obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj (Submonoid.powers f) x
    have hr : algebraMap R T r = 0 := by
      have h := congrArg φ he
      rw [map_mul, hx, zero_mul] at h
      exact (IsLocalization.Away.lift_eq f hunit r).symm.trans h.symm
    have hrA : algebraMap R A r = 0 := by
      have h := Ideal.mem_map_of_mem (algebraMap R A) (show r ∈ P from hr)
      rw [hmap, Ideal.map_bot] at h
      exact (Submodule.mem_bot A).mp h
    have hzero : x * algebraMap R A s.val = 0 := he.trans hrA
    apply (Ideal.unit_mul_mem_iff_mem (⊥ : Ideal A) (IsLocalization.map_units A s)).mp
    change algebraMap R A s.val * x = 0
    rw [mul_comm]
    exact hzero
  exact ⟨f, hf, hφ.isDomain φ⟩

end

variable {σ k R : Type*} [Field k] [IsAlgClosed k] [CommRing R] [Finite σ]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]

/-- The integral neighborhood retains the actual étale polynomial
coordinates and contains the specified closed point. -/
theorem exists_integral_etale_principal_neighborhood (q : Ideal R) [q.IsMaximal] :
    ∃ f ∉ q, Algebra.Etale (MvPolynomial σ k) (Localization.Away f) ∧
      IsDomain (Localization.Away f) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ k) R
  let : IsDomain (Localization.AtPrime q) := Blowups.Etale.LocalDomain.Construction.etale_closed_localRing_isDomain (σ := σ) (K := k) q
  obtain ⟨f, hf, hdomain⟩ := exists_domain_principal_neighborhood q
  let : Algebra.Etale R (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  exact ⟨f, hf, Algebra.Etale.comp (MvPolynomial σ k) R (Localization.Away f), hdomain⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.Neighborhood.Construction
