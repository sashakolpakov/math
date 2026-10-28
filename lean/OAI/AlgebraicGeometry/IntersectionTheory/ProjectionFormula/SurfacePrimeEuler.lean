import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.RankEuler
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Surface Prime Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler

noncomputable section

/-! In a two-dimensional local domain, the Euler characteristic of a
principal quotient against a finite torsion module is the sum of its
height-one prime-filtration contributions. Closed-point contributions vanish. -/

open _root_.CategoryTheory IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

theorem prime_height_one_or_maximal (hdim : (maximalIdeal R).height = 2)
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    p.asIdeal.height = 1 ∨ p.asIdeal = maximalIdeal R := by
  by_cases he : p.asIdeal = maximalIdeal R
  · exact Or.inr he
  left
  have hlt : p.asIdeal < maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) he
  have hheight := Ideal.height_strict_mono_of_isPrime hlt
  rw [hdim] at hheight
  apply le_antisymm (ENat.lt_two_iff.mp hheight)
  exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp)

omit [IsDomain R] [IsNoetherianRing R] in
theorem residue_quotient_length : Module.length R (R ⧸ maximalIdeal R) = 1 := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  rw [Module.length_eq_of_surjective (M := R ⧸ maximalIdeal R)
    (show Function.Surjective (algebraMap R (R ⧸ maximalIdeal R)) from Ideal.Quotient.mk_surjective)]
  exact Module.length_eq_one (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R)

theorem maximal_quotient_euler_zero (N : ModuleCat.{u} R) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hN : ∀ x : N, ∃ r : R, r ≠ 0 ∧ r • x = 0) :
    Tor.Euler.euler R (.of R (R ⧸ maximalIdeal R)) N d = 0 := by
  apply Generic.RankEuler.finite_length_torsion_euler_zero R _ N _ d hN
  rw [residue_quotient_length]
  exact ENat.one_ne_top

theorem isolated_principal_support (hdim : (maximalIdeal R).height = 2)
    (A : Type u) [CommRing A] [IsDomain A] [Algebra R A]
    (hker : RingHom.ker (algebraMap R A) ≠ ⊥) (r : R) (hr : algebraMap R A r ≠ 0) :
    Module.support R (QuotSMulTop r R) ∩ Module.support R A ⊆ {closedPoint R} := by
  let : (RingHom.ker (algebraMap R A)).IsPrime := Ideal.isPrime_bot.comap (algebraMap R A)
  intro q hq
  have hrq : r ∈ q.asIdeal := by
    have h := hq.1
    rw [Module.support_quotSMulTop] at h
    exact h.2 (Set.mem_singleton r)
  have hIq : RingHom.ker (algebraMap R A) ≤ q.asIdeal := by
    have h := hq.2
    rw [Module.support_of_algebra] at h
    exact h
  have hlt : RingHom.ker (algebraMap R A) < q.asIdeal := lt_of_le_of_ne hIq (by
    intro h
    exact hr (RingHom.mem_ker.mp (h ▸ hrq)))
  have hheight := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hI : 1 ≤ (RingHom.ker (algebraMap R A)).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hker)
  have htwo : 2 ≤ q.asIdeal.height := by
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ (RingHom.ker (algebraMap R A)).height + 1 := add_le_add hI le_rfl
      _ ≤ q.asIdeal.height := hheight
  have he : q.asIdeal = maximalIdeal R := q.asIdeal.eq_of_le_of_height_le
    (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) (by rw [hdim]; exact htwo)
  exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext he)

theorem exists_height_one_sum (hdim : (maximalIdeal R).height = 2)
    (r : R) (hr : r ≠ 0) (N : ModuleCat.{u} R) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hN : ∀ x : N, ∃ a : R, a ≠ 0 ∧ a • x = 0)
    (hisolated : Module.support R (QuotSMulTop r R) ∩ Module.support R N ⊆ {closedPoint R}) :
    ∃ (n : ℕ) (primes : Fin n → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (primes i).asIdeal) ⊆ Module.support R (QuotSMulTop r R)) ∧
      Tor.Euler.euler R (.of R (QuotSMulTop r R)) N d =
        ∑ i ∈ Finset.univ.filter (fun i => (primes i).asIdeal.height = 1),
          Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) N d := by
  classical
  obtain ⟨n, primes, hsupp, he⟩ := PrimeFiltrationEuler.exists_prime_sum R
    (.of R (QuotSMulTop r R)) N d (closedPoint R) hisolated
  refine ⟨n, primes, hsupp, ?_⟩
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hp : primes i ∈ Module.support R (R ⧸ (primes i).asIdeal) := by
    rw [Module.mem_support_iff']
    refine ⟨1, fun a ha hz => ha ?_⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change algebraMap R (R ⧸ (primes i).asIdeal) a = 0
    simpa only [Algebra.smul_def, mul_one] using hz
  have hmem := hsupp i hp
  rw [Module.support_quotSMulTop] at hmem
  have hrp : r ∈ (primes i).asIdeal := hmem.2 (Set.mem_singleton r)
  have hne : (primes i).asIdeal ≠ ⊥ := by
    intro hz
    rw [hz, Submodule.mem_bot] at hrp
    exact hr hrp
  have hh : (primes i).asIdeal.height ≠ 1 := by simpa only [Finset.mem_filter, Finset.mem_univ,
    true_and] using hi
  have hmax := (prime_height_one_or_maximal R hdim (primes i) hne).resolve_left hh
  rw [hmax]
  exact maximal_quotient_euler_zero R N d hN

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
