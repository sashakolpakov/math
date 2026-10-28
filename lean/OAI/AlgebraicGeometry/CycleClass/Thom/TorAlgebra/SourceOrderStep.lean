import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEquationEulerStep
import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime

/-! # Source Order Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep

noncomputable section

/-! The regular-equation reduction of a source quotient, with every
coefficient written as the actual order in its canonical source local ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.MinimalSupportPrimes.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ResidualMinimalSourcePrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] (P : Ideal R) (r : R)

abbrev ResidualComponent :=
  ↥(MinimalSupportPrimes.Constructions.minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)))

def residualSourcePrime (p : ResidualComponent R P r) : PrimeSpectrum (R ⧸ P) :=
  ResidualMinimalSourcePrime.Constructions.minimalSourcePrime R P r p.val
    ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p.val).mp p.property)

variable [IsLocalRing R] (rs : List R)
  (hr : IsWeaklyRegular R (r :: rs))
  (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R)
  (hn : IsSMulRegular (R ⧸ P) r)
  (hd : Module.supportDim R (R ⧸ P) ≤ ((r :: rs).length : WithBot ℕ∞))
  (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R (R ⧸ P) ⊆
    {IsLocalRing.closedPoint R})

include hr hm hn hd hi

theorem euler_eq_source_order_sum (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) (ModuleCat.of R (R ⧸ P)) d =
      ∑ p : ResidualComponent R P r,
        ((Ring.ord (Localization.AtPrime (residualSourcePrime R P r p).asIdeal)
          (algebraMap (R ⧸ P) (Localization.AtPrime (residualSourcePrime R P r p).asIdeal)
            (algebraMap R (R ⧸ P) r))).toNat : ℚ) *
          Euler.Tor.euler (R ⧸ Ideal.span {r})
            (ModuleCat.of (R ⧸ Ideal.span {r})
              ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
            (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ p.val.asIdeal)) d := by
  rw [RegularEquationEulerStep.euler_eq_residual_prime_sum R
    (ModuleCat.of R (R ⧸ P)) r rs hr hm hn hd hi d hD]
  symm
  trans ∑ p : ResidualComponent R P r,
    ((LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p.val).toNat : ℚ) *
      Euler.Tor.euler (R ⧸ Ideal.span {r})
        (ModuleCat.of (R ⧸ Ideal.span {r})
          ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
        (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ p.val.asIdeal)) d
  · apply Finset.sum_congr rfl
    intro p _
    rw [ResidualMinimalSourcePrime.Constructions.localLength_eq_minimalSourcePrime_ord R P r p.val
      ((MinimalSupportPrimes.Constructions.mem_minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p.val).mp p.property)]
    rfl
  · exact Finset.sum_coe_sort
      (MinimalSupportPrimes.Constructions.minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)))
      (fun p : PrimeSpectrum (R ⧸ Ideal.span {r}) =>
        ((LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r (R ⧸ P)) p).toNat : ℚ) *
          Euler.Tor.euler (R ⧸ Ideal.span {r})
            (ModuleCat.of (R ⧸ Ideal.span {r})
              ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
            (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ p.asIdeal)) d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep
