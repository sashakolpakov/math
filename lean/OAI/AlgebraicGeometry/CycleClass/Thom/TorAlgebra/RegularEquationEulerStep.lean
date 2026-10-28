import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEulerMultiplicity

/-! # Regular Equation Euler Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEquationEulerStep

noncomputable section

/-! A regular first equation reduces the native intersection Euler
sum to the residual minimal-prime cycles, with actual local lengths. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotientSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N] (r : R) (rs : List R)
  (hr : IsWeaklyRegular R (r :: rs))
  (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R)
  (hn : IsSMulRegular N r)
  (hd : Module.supportDim R N ≤ ((r :: rs).length : WithBot ℕ∞))
  (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R N ⊆
    {IsLocalRing.closedPoint R})

include hr hm hn hd hi

theorem euler_eq_residual_prime_sum (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) N d =
      ∑ p ∈ MinimalSupportPrimes.Constructions.minimalSupportPrimes (R ⧸ Ideal.span {r}) (QuotSMulTop r N),
        ((LocalizedModuleLength.Constructions.localLength (R ⧸ Ideal.span {r}) (QuotSMulTop r N) p).toNat : ℚ) *
          Euler.Tor.euler (R ⧸ Ideal.span {r})
            (ModuleCat.of (R ⧸ Ideal.span {r})
              ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
            (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ p.asIdeal)) d := by
  let : IsLocalRing (R ⧸ Ideal.span {r}) := Regular.EquationQuotientSupport.Constructions.quotientLocalRing R r (hm r (List.mem_cons_self))
  let : Module.Finite (R ⧸ Ideal.span {r}) (QuotSMulTop r N) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {r}) _
  let tail := rs.map (algebraMap R (R ⧸ Ideal.span {r}))
  have hrt : IsWeaklyRegular (R ⧸ Ideal.span {r}) tail := Regular.EquationQuotients.Constructions.weaklyRegular_tail R r rs hr
  have hmt : ∀ x ∈ tail, x ∈ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}) :=
    Regular.EquationQuotientSupport.Constructions.maximalIdeal_tail R r rs (fun x hx => hm x (List.mem_cons_of_mem r hx))
  have hdt : Module.supportDim (R ⧸ Ideal.span {r}) (QuotSMulTop r N) ≤ (tail.length : WithBot ℕ∞) := by
    rw [Regular.EquationQuotientSupport.Constructions.quotient_supportDim R r N]
    simp only [tail, List.length_map]
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    rw [Module.supportDim_quotSMulTop_succ_eq_supportDim hn (hm r (List.mem_cons_self))]
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hd
  have hit := Regular.EquationQuotientSupport.Constructions.isolated_tail R r N rs hi
  exact (SequenceChangeOfRings.euler_eq R r rs N
    ((isWeaklyRegular_cons_iff R r rs).mp hr).1 hn d).trans
      (RegularEulerMultiplicity.euler_eq_minimalSupportPrimes_sum
        (R ⧸ Ideal.span {r}) (ModuleCat.of (R ⧸ Ideal.span {r}) (QuotSMulTop r N))
        tail hrt hmt hdt hit d (by simpa only [tail, List.length_map] using hD))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularEquationEulerStep
