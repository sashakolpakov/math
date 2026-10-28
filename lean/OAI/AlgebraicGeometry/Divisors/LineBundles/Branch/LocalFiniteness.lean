import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal

/-! # Local Finiteness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.LocalFiniteness.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local exactness at P suffices for branch homology finiteness

This applies to any two endomorphisms of the actual branch image,
including the complementary powers of a chosen uniformizer.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 2 R]

theorem branchLocalized_exact_off_closed (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (φ ψ : PeriodicComplex.BundleCycles.productBranchModule a b P →ₗ[R] PeriodicComplex.BundleCycles.productBranchModule a b P)
    (hlocal : Function.Exact (Periodic.Localization.BundleCycles.localizedEndomorphism P.primeCompl φ) (Periodic.Localization.BundleCycles.localizedEndomorphism P.primeCompl ψ))
    (q : PrimeSpectrum R) (hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Function.Exact (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl φ) (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl ψ) := by
  by_cases hpq : P ≤ q.asIdeal
  · have he := Diagonal.BundleCycles.surfaceMinimalPrime_le_eq_of_not_maximal (a * b) (mul_ne_zero ha hb) P hP q hqm hpq
    subst P
    exact hlocal
  · have hz : Subsingleton (LocalizedModule q.asIdeal.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P)) :=
      MinimalBranchSupport.BundleCycles.minimalPrime_branch_localization_zero (Ideal.span {a * b}) P hP q hpq
    intro m
    constructor
    · intro _
      exact ⟨0, hz.elim _ _⟩
    · intro _
      exact hz.elim _ _

theorem branchPeriodicHomology_length_ne_top [IsNoetherianRing R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (φ ψ : PeriodicComplex.BundleCycles.productBranchModule a b P →ₗ[R] PeriodicComplex.BundleCycles.productBranchModule a b P)
    (hψφ : φ.comp ψ = 0)
    (hlocal : Function.Exact (Periodic.Localization.BundleCycles.localizedEndomorphism P.primeCompl ψ) (Periodic.Localization.BundleCycles.localizedEndomorphism P.primeCompl φ)) :
    Module.length R (Periodic.Exact.BundleCycles.periodicHomology φ ψ hψφ) ≠ ⊤ :=
  Periodic.Localization.BundleCycles.periodicHomology_length_ne_top_of_local_exact φ ψ hψφ
    (branchLocalized_exact_off_closed a b ha hb P hP ψ φ hlocal)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.LocalFiniteness.BundleCycles
