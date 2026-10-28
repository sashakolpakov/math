import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceParameters
import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeIntersectionLength
import OAI.AlgebraicGeometry.Divisors.LineBundles.WholeFiltration
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Surface Filtration Expansion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: local surface intersection expanded over prime supports

For proper parameters on a two-dimensional Noetherian local domain,
every prime factor contributes its actual quotient length on a minimal
prime support. All other factors are residue-field factors and have zero
Euler contribution. The resulting expansion is proved for every actual
prime filtration.
-/

variable {R : Type*} [CommRing R]

def SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight (a b : R) (P : Ideal R) : ℤ := by
  classical
  exact if P ∈ (Ideal.span {b}).minimalPrimes then PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P else 0

variable [IsNoetherianRing R] [IsDomain R] [IsLocalRing R]
variable (a b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
variable (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)

include hb hdim

theorem SurfaceFiltrationExpansion.BundleCycles.surfacePrimeEuler_eq_weight (J : Ideal R) [J.IsPrime] (hbJ : b ∈ J) :
    EquationFiniteLength.BundleCycles.twoEquationEulerLength a b (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hab)
      (LocalizedPrimeFactor.BundleCycles.idealQuotient_annihilated J b hbJ) = SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b J := by
  classical
  let : Ring.KrullDimLE 2 R := Ring.krullDimLE_iff.mpr hdim.le
  by_cases hJ : J ∈ (Ideal.span {b}).minimalPrimes
  · rw [SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight, ite_eq_left hJ]
    exact PrimeIntersectionLength.BundleCycles.twoEquationEulerLength_prime a J b _ hbJ (SurfaceParameters.BundleCycles.surfaceParameter_not_mem_minimal a b hdim hab J hJ)
  · rw [SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight, ite_eq_right hJ]
    have he := (SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal b hb J hbJ).resolve_left hJ
    apply TwoEquationEulerFunctorial.BundleCycles.twoEquationEulerLength_zero_of_finite
    apply Module.length_ne_top_iff.mpr
    apply LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal
    exact (Ideal.IsPrime.radical ‹J.IsPrime›).trans he

section

theorem PrimeFiltration.BundleCycles.PrimeFiltrationAbove.surface_eulerSum_eq {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hbM : Module.IsTorsionBy R M b) {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) :
    F.eulerSum a b (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hab) hbM =
      (F.factors.map (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b)).sum := by
  induction F with
  | top => rfl
  | step N L hNL J hJ e tail ih =>
    let : J.IsPrime := hJ
    have hbJ := LocalizedPrimeFactor.BundleCycles.annihilator_mem_ideal J b (PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated b hbM N L J e)
    exact congrArg₂ (· + ·) (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeEuler_eq_weight a b hb hdim hab J hbJ) ih

end

/-- The actual intersection length expanded over an arbitrary prime filtration of R/bR. -/
theorem SurfaceFiltrationExpansion.BundleCycles.localIntersectionLength_eq_filtration_sum
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R (MultiplicationSequence.BundleCycles.equationCokernel b R))) :
    LocalIntersectionLength.BundleCycles.localIntersectionLength a b (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hab) =
      (F.factors.map (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b)).sum :=
  (F.whole_eulerSum_eq a b _ (LocalIntersectionLength.BundleCycles.equationCokernel_annihilated b R)).symm.trans
    (F.surface_eulerSum_eq a b hb hdim hab (LocalIntersectionLength.BundleCycles.equationCokernel_annihilated b R))

/-- Group repeated prime factors, keeping their proved occurrence multiplicities. -/
theorem SurfaceFiltrationExpansion.BundleCycles.localIntersectionLength_eq_filtration_weighted_sum
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R (MultiplicationSequence.BundleCycles.equationCokernel b R))) :
    LocalIntersectionLength.BundleCycles.localIntersectionLength a b (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hab) =
      ∑ J ∈ F.factors.toFinset, F.factors.count J • SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b J :=
  (SurfaceFiltrationExpansion.BundleCycles.localIntersectionLength_eq_filtration_sum a b hb hdim hab F).trans
    (Finset.sum_list_map_count F.factors (SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
