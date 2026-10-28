import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! # Support Nonminimal Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportNonminimalDimension.Constructions

noncomputable section

/-! Nonminimal primes in a finite-dimensional module support have
strictly smaller quotient dimension. No catenarity assumption is used. -/

universe u v
variable (R : Type u) [CommRing R]

theorem supportDim_primeQuotient (p : PrimeSpectrum R) :
    Module.supportDim R (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  have hs : Module.support R (R ⧸ p.asIdeal) = Set.Ici p := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    rfl
  rw [Module.supportDim, hs, ← Order.coheight_eq_krullDim_Ici]

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem support_primeQuotient_subset (p : PrimeSpectrum R)
    (hp : Module.annihilator R M ≤ p.asIdeal) :
    Module.support R (R ⧸ p.asIdeal) ⊆ Module.support R M := by
  intro q hq
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hq
  exact Module.mem_support_iff_of_finite.mpr (hp.trans hq)

theorem nonminimal_supportDim_lt (d : ℕ) (hd : Module.supportDim R M ≤ (d : WithBot ℕ∞))
    (q : PrimeSpectrum R) (hq : q ∈ Module.support R M)
    (hn : q.asIdeal ∉ (Module.annihilator R M).minimalPrimes) :
    Module.supportDim R (R ⧸ q.asIdeal) < (d : WithBot ℕ∞) := by
  obtain ⟨I, hI, hle⟩ := Ideal.exists_minimalPrimes_le (Module.mem_support_iff_of_finite.mp hq)
  let p : PrimeSpectrum R := ⟨I, hI.isPrime⟩
  have hlt : p < q := lt_of_le_of_ne hle (by
    intro he
    exact hn (congrArg PrimeSpectrum.asIdeal he ▸ hI))
  have hs : Module.support R (R ⧸ p.asIdeal) ⊆ Module.support R M :=
    support_primeQuotient_subset R M p hI.le
  have hdim : Module.supportDim R (R ⧸ p.asIdeal) ≤ Module.supportDim R M :=
    Order.krullDim_le_of_strictMono (fun z => ⟨z.val, hs z.property⟩)
      (fun {_ _} h => h)
  have hadd : Module.supportDim R (R ⧸ q.asIdeal) + 1 ≤ Module.supportDim R (R ⧸ p.asIdeal) := by
    rw [supportDim_primeQuotient, supportDim_primeQuotient]
    exact_mod_cast Order.coheight_add_one_le hlt
  exact ENat.WithBot.add_one_le_natCast_iff.mp (hadd.trans (hdim.trans hd))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportNonminimalDimension.Constructions
