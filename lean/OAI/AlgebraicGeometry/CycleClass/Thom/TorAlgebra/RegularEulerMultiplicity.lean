import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrimeEulerLength
import OAI.AlgebraicGeometry.CycleClass.Thom.PrimeFiltrationMultiplicity
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportNonminimalDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularSequenceVanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes

/-! # Regular Euler Multiplicity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEulerMultiplicity

noncomputable section

/-! Associativity of regular-sequence Euler multiplicities: only
minimal source primes contribute, weighted by their actual local lengths.
Nonminimal prime factors vanish by the proved dimension theorem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor
open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrimeFiltrationMultiplicity.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (rs : List R)
  (hr : IsWeaklyRegular R rs) (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
  (hd : Module.supportDim R M ≤ (rs.length : WithBot ℕ∞))
  (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R M ⊆
    {IsLocalRing.closedPoint R})

include hr hm hd hi

theorem euler_eq_sum_minimal_localLengths (s : Finset (PrimeSpectrum R))
    (hs : ∀ p, p ∈ s ↔ p.asIdeal ∈ (Module.annihilator R M).minimalPrimes) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) M rs.length =
      ∑ p ∈ s, ((LocalizedModuleLength.Constructions.localLength R M p).toNat : ℚ) *
        Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R (R ⧸ p.asIdeal)) rs.length := by
  let T := ModuleCat.of R (R ⧸ Ideal.ofList rs)
  let e := fun p : PrimeSpectrum R => Euler.Tor.euler R T (ModuleCat.of R (R ⧸ p.asIdeal)) rs.length
  let := Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  have hI : Module.support R (R ⧸ Ideal.ofList rs) =
      PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hMT : Module.support R M ∩ Module.support R T ⊆ {IsLocalRing.closedPoint R} := by
    change Module.support R M ∩ Module.support R (R ⧸ Ideal.ofList rs) ⊆ _
    rw [hI, Set.inter_comm]
    exact hi
  obtain ⟨ps, hps, he, hl⟩ := PrimeEulerLength.exists_prime_euler_localLength_sum
    R T rs.length M (IsLocalRing.closedPoint R) hMT
  have hE : Euler.Tor.euler R T M rs.length = (ps.map e).sum := by
    rw [EulerTransport.Tor.comm R T M, he]
    congr 1
    apply List.map_congr_left
    intro p _
    exact EulerTransport.Tor.comm R _ T rs.length
  have hc (p : PrimeSpectrum R) (hp : p ∈ s) :
      ((LocalizedModuleLength.Constructions.localLength R M p).toNat : ℚ) = (ps.count p : ℚ) := by
    rw [PrimeFiltrationMultiplicity.Constructions.localLength_eq_count R M p ((hs p).mp hp) ps hps (hl p), ENat.toNat_natCast]
  have hz (p : PrimeSpectrum R) (hp : p ∈ ps.toFinset) (hn : p ∉ s) : e p = 0 := by
    have hpM : p ∈ Module.support R M := hps p (List.mem_toFinset.mp hp) (by
      rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient])
    have hdim := SupportNonminimalDimension.Constructions.nonminimal_supportDim_lt R M rs.length hd
      p hpM (fun h => hn ((hs p).mpr h))
    have his : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R (R ⧸ p.asIdeal) ⊆
        {IsLocalRing.closedPoint R} :=
      (Set.inter_subset_inter_right _ (hps p (List.mem_toFinset.mp hp))).trans hi
    exact RegularSequenceVanishing.euler_eq_zero R (ModuleCat.of R (R ⧸ p.asIdeal))
      rs hr hm hdim his
  have hU : (∑ p ∈ ps.toFinset, (ps.count p : ℚ) * e p) =
      ∑ p ∈ ps.toFinset ∪ s, (ps.count p : ℚ) * e p := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p _ hp
    have hc0 : ps.count p = 0 := List.count_eq_zero.mpr (fun h => hp (List.mem_toFinset.mpr h))
    rw [hc0, Nat.cast_zero, zero_mul]
  have hS : (∑ p ∈ s, (ps.count p : ℚ) * e p) =
      ∑ p ∈ ps.toFinset ∪ s, (ps.count p : ℚ) * e p := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hn
    rw [hz p ((Finset.mem_union.mp hp).resolve_right hn) hn, mul_zero]
  calc
    _ = (ps.map e).sum := hE
    _ = ∑ p ∈ ps.toFinset, (ps.count p : ℚ) * e p := by
      rw [Finset.sum_list_map_count]
      simp only [nsmul_eq_mul]
    _ = ∑ p ∈ s, (ps.count p : ℚ) * e p := hU.trans hS.symm
    _ = _ := Finset.sum_congr rfl (fun p hp => congrArg (· * e p) (hc p hp).symm)

theorem euler_eq_sum_minimal_localLengths_above_length (s : Finset (PrimeSpectrum R))
    (hs : ∀ p, p ∈ s ↔ p.asIdeal ∈ (Module.annihilator R M).minimalPrimes)
    (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) M d =
      ∑ p ∈ s, ((LocalizedModuleLength.Constructions.localLength R M p).toNat : ℚ) *
        Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R (R ⧸ p.asIdeal)) d := by
  let := Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  rw [EulerCutoff.stable_left R _ M rs.length d hD,
    euler_eq_sum_minimal_localLengths R M rs hr hm hd hi s hs]
  apply Finset.sum_congr rfl
  intro p _
  rw [EulerCutoff.stable_left R _ (ModuleCat.of R (R ⧸ p.asIdeal)) rs.length d hD]

theorem euler_eq_minimalSupportPrimes_sum (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) M d =
      ∑ p ∈ MinimalSupportPrimes.Constructions.minimalSupportPrimes R M,
        ((LocalizedModuleLength.Constructions.localLength R M p).toNat : ℚ) *
          Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R (R ⧸ p.asIdeal)) d :=
  euler_eq_sum_minimal_localLengths_above_length R M rs hr hm hd hi _
    (MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes R M) d hD

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEulerMultiplicity
