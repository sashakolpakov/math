import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.AuxiliaryParameter
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceFiltrationExpansion

/-! # Filtration Weight -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: prime-filtration weights for a module supported on one branch

Every actual factor contains the radical of the module annihilator.
On a local surface, its prime is therefore the branch prime or the
closed point. Only the branch factors contribute to the Euler length.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.factor_contains_annihilator_radical
    {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) (J : Ideal R) (hJ : J ∈ F.factors) :
    (Module.annihilator R M).radical ≤ J :=
  (F.factor_isPrime J hJ).radical_le_iff.mpr (fun x hx =>
    F.factor_contains_annihilator x (fun {m} => Module.mem_annihilator.mp hx m) J hJ)

variable [IsNoetherianRing R] [IsDomain R] [IsLocalRing R]

theorem Branch.FiltrationWeight.BundleCycles.branchFiltration_factor_maximal_of_ne (r : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hAnn : (Module.annihilator R M).radical = P)
    {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) (J : Ideal R)
    (hJ : J ∈ F.factors) (hJP : J ≠ P) : J = IsLocalRing.maximalIdeal R := by
  let branchWeightPrime : J.IsPrime := F.factor_isPrime J hJ
  let branchWeightDimension : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  have hpj : P ≤ J := hAnn ▸ F.factor_contains_annihilator_radical J hJ
  have hrJ := hpj (hP.le (Ideal.subset_span (Set.mem_singleton r)))
  rcases SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal r hr J hrJ with hmin | he
  · exact False.elim (hJP (Branch.AuxiliaryParameter.BundleCycles.minimalPrincipalPrimes_comparable_eq r r hr P J hP hmin hpj).symm)
  · exact he

theorem Branch.FiltrationWeight.BundleCycles.branchFiltration_weight (r x y : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes)
    (hPy : P ∈ (Ideal.span {y}).minimalPrimes) (hAnn : (Module.annihilator R M).radical = P)
    {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) (J : Ideal R) (hJ : J ∈ F.factors) :
    SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight x y J = if J = P then PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength x P else 0 := by
  classical
  by_cases he : J = P
  · subst J
    rw [ite_eq_left rfl, SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight, ite_eq_left hPy]
  · rw [ite_eq_right he, SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight]
    apply ite_eq_right
    intro hmin
    exact Branch.AuxiliaryParameter.BundleCycles.minimalPrincipalPrime_ne_maximal y hdim J hmin
      (Branch.FiltrationWeight.BundleCycles.branchFiltration_factor_maximal_of_ne r hr hdim P hP hAnn F J hJ he)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
