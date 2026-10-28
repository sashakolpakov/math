import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Order
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.LocalTwoBound
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeQuotientLocalization

/-! # Prime Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler

noncomputable section

/-! A proper local parameter fiber is computed by an actual prime
filtration. Closed-point factors contribute zero, and every remaining
factor contributes its native order of vanishing of the parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Pointwise Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

def quotientEquiv (r : R) : (R ⧸ Ideal.span {r}) ≃ₗ[R] QuotSMulTop r R :=
  Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])

omit [IsNoetherianRing R] [IsLocalRing R] in
theorem quotient_bound (r : R) (hr : r ≠ 0) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span {r})) 1 := by
  let : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop r R)) 1 :=
    Regular.LocalTwoBound.quotient_bound R (.of R R) r (IsSMulRegular.of_ne_zero hr) 0
  exact hasProjectiveDimensionLT_of_iso (quotientEquiv R r).symm.toModuleIso 2

theorem closed_euler_zero (r : R) (hr : r ≠ 0) :
    Tor.Euler.euler R (.of R (R ⧸ maximalIdeal R)) (.of R (R ⧸ Ideal.span {r})) 1 = 0 := by
  let := quotient_bound R r hr
  exact SurfacePrimeEuler.maximal_quotient_euler_zero R (.of R (R ⧸ Ideal.span {r})) 1
    (fun x => ⟨r, hr, PrimeQuotientLocalization.annihilated R (Ideal.span {r}) r (Ideal.subset_span rfl) x⟩)

omit [IsNoetherianRing R] [IsLocalRing R] in
theorem prime_euler (r : R) (hr : r ≠ 0) (p : PrimeSpectrum R) (hp : r ∉ p.asIdeal) :
    Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1 =
      ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) :=
  Principal.Order.euler_eq_order_of_equiv R (R ⧸ p.asIdeal) Ideal.Quotient.mk_surjective
    r (IsSMulRegular.of_ne_zero hr) (Ideal.Quotient.eq_zero_iff_mem.not.mpr hp)
    (.of R (R ⧸ Ideal.span {r})) (quotientEquiv R r) 1

theorem exists_order_sum (r : R) (hr : r ≠ 0) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hisolated : Module.support R M ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R}) :
    ∃ (k : ℕ) (primes : Fin k → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (primes i).asIdeal) ⊆ Module.support R M) ∧
      (∀ i, primes i ≠ closedPoint R → r ∉ (primes i).asIdeal) ∧
      Tor.Euler.euler R M (.of R (R ⧸ Ideal.span {r})) 1 =
        ∑ i ∈ Finset.univ.filter (fun i => primes i ≠ closedPoint R),
          ((Ring.ord (R ⧸ (primes i).asIdeal) (Ideal.Quotient.mk (primes i).asIdeal r)).toNat : ℚ) := by
  let := quotient_bound R r hr
  obtain ⟨k, primes, hsupp, he⟩ := PrimeFiltrationEuler.exists_prime_sum R M
    (.of R (R ⧸ Ideal.span {r})) 1 (closedPoint R) hisolated
  have havoid (i : Fin k) (hi : primes i ≠ closedPoint R) : r ∉ (primes i).asIdeal := by
    intro hri
    apply hi
    apply Set.mem_singleton_iff.mp (hisolated ?_)
    constructor
    · apply hsupp i
      rw [Module.mem_support_iff']
      refine ⟨1, fun a ha hz => ha ?_⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change algebraMap R (R ⧸ (primes i).asIdeal) a = 0
      simpa only [Algebra.smul_def, mul_one] using hz
    · rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
      exact Ideal.span_le.mpr (fun a ha => (Set.mem_singleton_iff.mp ha).symm ▸ hri)
  refine ⟨k, primes, hsupp, havoid, ?_⟩
  have hfilter : (∑ i ∈ Finset.univ.filter (fun i => primes i ≠ closedPoint R),
      Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1) =
      ∑ i : Fin k, Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hp : primes i = closedPoint R := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
    rw [hp]
    exact closed_euler_zero R r hr
  rw [he, ← hfilter]
  apply Finset.sum_congr rfl
  intro i hi
  exact prime_euler R r hr (primes i) (havoid i (Finset.mem_filter.mp hi).2)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.PrimeEuler
