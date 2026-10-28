import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceFiltrationExpansion
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationLength
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Surface Intersection Formula -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceIntersectionFormula.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local surface intersection formula with actual multiplicities

The finite sum over minimal prime supports uses the actual local length
of R_P/bR_P and the actual length of R/(P+(a)). The constructed prime
filtration proves that this sum is the multiplication Euler length.
Thus the expression depends only on the equations and their local rings.
-/

variable {R : Type*} [CommRing R]

def surfaceIntersectionSummand (a b : R) (P : Ideal R) : ℤ := by
  classical
  exact if hP : P ∈ (Ideal.span {b}).minimalPrimes then
    (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP.isPrime : ℤ) * PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P else 0

variable [IsNoetherianRing R]

/-- The actual finite local intersection sum over the prime components of b = 0. -/
def surfaceIntersectionNumber (a b : R) : ℤ :=
  ∑ P ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset,
    surfaceIntersectionSummand a b P

omit [IsNoetherianRing R] in
theorem primeEquationMultiplicity_eq_count (b : R) (P : Ideal R)
    (hP : P ∈ (Ideal.span {b}).minimalPrimes)
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R (MultiplicationSequence.BundleCycles.equationCokernel b R))) :
    LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP.isPrime = F.factors.count P := by
  let : P.IsPrime := hP.isPrime
  have h := F.whole_localized_length_eq_count b (LocalIntersectionLength.BundleCycles.equationCokernel_annihilated b R) P hP
  rw [(LocalizedEquationLength.BundleCycles.localizedEquationCokernelEquiv P.primeCompl b).length_eq] at h
  have hn := congrArg ENat.toNat h
  simpa only [LocalizedEquationLength.BundleCycles.primeEquationMultiplicity, ENat.toNat_natCast] using hn

omit [IsNoetherianRing R] in
theorem surface_filtration_summand (a b : R)
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R (MultiplicationSequence.BundleCycles.equationCokernel b R))) (P : Ideal R) :
    F.factors.count P • SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b P = surfaceIntersectionSummand a b P := by
  classical
  by_cases hP : P ∈ (Ideal.span {b}).minimalPrimes
  · rw [SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight, ite_eq_left hP, surfaceIntersectionSummand, dite_eq_left hP,
      primeEquationMultiplicity_eq_count b P hP F, nsmul_eq_mul]
  · rw [SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight, ite_eq_right hP, surfaceIntersectionSummand, dite_eq_right hP, smul_zero]

theorem surface_filtration_weighted_sum (a b : R)
    (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove (⊥ : Submodule R (MultiplicationSequence.BundleCycles.equationCokernel b R))) :
    (∑ P ∈ F.factors.toFinset, F.factors.count P • SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b P) =
      surfaceIntersectionNumber a b := by
  classical
  let S := (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset
  let T := F.factors.toFinset ∪ S
  have hF : (∑ P ∈ F.factors.toFinset, F.factors.count P • SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b P) =
      ∑ P ∈ T, F.factors.count P • SurfaceFiltrationExpansion.BundleCycles.surfacePrimeIntersectionWeight a b P := by
    apply Finset.sum_subset Finset.subset_union_left
    intro P hPT hPF
    rw [List.count_eq_zero_of_not_mem (fun h => hPF (List.mem_toFinset.mpr h)), zero_smul]
  have hS : (∑ P ∈ S, surfaceIntersectionSummand a b P) =
      ∑ P ∈ T, surfaceIntersectionSummand a b P := by
    apply Finset.sum_subset Finset.subset_union_right
    intro P hPT hPS
    have hp : P ∉ (Ideal.span {b}).minimalPrimes :=
      fun h => hPS ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).mem_toFinset.mpr h)
    rw [surfaceIntersectionSummand, dite_eq_right hp]
  exact hF.trans ((Finset.sum_congr rfl (fun P _ => surface_filtration_summand a b F P)).trans hS.symm)

variable [IsDomain R] [IsLocalRing R]

/-- The local intersection sum is the finite Euler length of the two actual equations. -/
theorem surfaceIntersectionNumber_eq_localIntersectionLength (a b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceIntersectionNumber a b =
      LocalIntersectionLength.BundleCycles.localIntersectionLength a b (LocalIntersectionFiniteness.BundleCycles.finiteLength_quotient_of_radical_maximal _ hab) := by
  let F := PrimeFiltration.BundleCycles.modulePrimeFiltration (R := R) (M := MultiplicationSequence.BundleCycles.equationCokernel b R)
  exact (surface_filtration_weighted_sum a b F).symm.trans
    (SurfaceFiltrationExpansion.BundleCycles.localIntersectionLength_eq_filtration_weighted_sum a b hb hdim hab F).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceIntersectionFormula.BundleCycles
