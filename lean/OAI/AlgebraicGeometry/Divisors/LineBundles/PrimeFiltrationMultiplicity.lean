import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedPrimeFactor
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! # Prime Filtration Multiplicity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltrationMultiplicity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: filtration multiplicities are actual local module lengths

Every prime cyclic factor contains each equation annihilating the module.
At a prime minimal over such an equation, all localized factors vanish
except R/P, whose length is one. The number of occurrences of P in an
actual prime filtration is therefore the length at P.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace PrimeFiltrationAbove

theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltration.BundleCycles.PrimeFiltrationAbove.factor_contains_annihilator (b : R) (hb : Module.IsTorsionBy R M b)
    {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) (J : Ideal R) (hJ : J ∈ F.factors) : b ∈ J := by
  induction F with
  | top => exact False.elim (List.not_mem_nil hJ)
  | step N L hNL K hK e tail ih =>
    rcases List.mem_cons.mp hJ with rfl | h
    · exact LocalizedPrimeFactor.BundleCycles.annihilator_mem_ideal J b (PrimeFiltrationEuler.BundleCycles.primeFactor_annihilated b hb N L J e)
    · exact ih h

end PrimeFiltrationAbove

theorem localizedPrimeFactorLength_minimal (b : R) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {b}).minimalPrimes) (J : Ideal R) (hJ : J.IsPrime) (hbJ : b ∈ J) :
    LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength P.primeCompl J = if J = P then 1 else 0 := by
  classical
  by_cases he : J = P
  · subst J
    rw [ite_eq_left rfl]
    exact LocalizedPrimeFactor.BundleCycles.localizedPrimeFactorLength_self P
  · rw [ite_eq_right he]
    apply LocalizedPrimeFactor.BundleCycles.localizedPrimeFactorLength_zero P J
    intro hJP
    exact he (le_antisymm hJP (hP.2 ⟨hJ, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJ)⟩ hJP))

private theorem sum_ideal_indicators (L : List (Ideal R)) (P : Ideal R) :
    (L.map (fun J => if J = P then (1 : ℕ∞) else 0)).sum = (L.count P : ℕ∞) := by
  classical
  induction L with
  | nil => simp
  | cons J L ih =>
    by_cases h : J = P
    · subst J
      simp [ih, add_comm]
    · simp [h, ih]

namespace PrimeFiltrationAbove

/-- A prime's filtration multiplicity is the actual length after localization at that prime. -/
theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltration.BundleCycles.PrimeFiltrationAbove.localized_length_eq_count (b : R) (hb : Module.IsTorsionBy R M b)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {b}).minimalPrimes)
    {N : Submodule R M} (F : PrimeFiltration.BundleCycles.PrimeFiltrationAbove N) :
    Module.length (Localization P.primeCompl) (LocalizedModule P.primeCompl (M ⧸ N)) =
      (F.factors.count P : ℕ∞) := by
  classical
  rw [F.localized_length_eq_sum P.primeCompl]
  have hw : F.factors.map (LocalizedFiltrationLength.BundleCycles.localizedPrimeFactorLength P.primeCompl) =
      F.factors.map (fun J => if J = P then (1 : ℕ∞) else 0) := by
    apply List.map_congr_left
    intro J hJ
    exact localizedPrimeFactorLength_minimal b P hP J (F.factor_isPrime J hJ)
      (F.factor_contains_annihilator b hb J hJ)
  rw [hw]
  exact sum_ideal_indicators F.factors P

end PrimeFiltrationAbove

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeFiltrationMultiplicity.BundleCycles
