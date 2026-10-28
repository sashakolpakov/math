import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularPrimeDevissage
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.PrimeEquation
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SequenceChangeOfRings

/-! # Regular Sequence Vanishing -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularSequenceVanishing

noncomputable section

/-! Dimension vanishing for the native Tor Euler characteristic of a
regular-sequence quotient against an arbitrary finite module over a
Noetherian local ring. The proof uses actual prime filtrations and
regular change of rings; the intermediate rings may be singular. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularPrimeDevissage
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotientSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients.Constructions

set_option backward.isDefEq.respectTransparency false

universe u

theorem euler_eq_zero_of_length (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (N : ModuleCat.{u} R) [Module.Finite R N] (rs : List R), rs.length = n →
      IsWeaklyRegular R rs → (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) →
      Module.supportDim R N < (rs.length : WithBot ℕ∞) →
      PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R N ⊆
        {IsLocalRing.closedPoint R} →
      Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N rs.length = 0 := by
  induction n with
  | zero =>
    intro R _ _ _ N _ rs hlen _ _ hd _
    exact RegularPrimeDevissage.euler_eq_zero_of_supportDim_lt_zero R _ N (by simpa only [hlen, Nat.cast_zero] using hd) _
  | succ n ih =>
    intro R _ _ _ N _ xs hlen hr hm hd hi
    cases xs with
    | nil => simp at hlen
    | cons r rs =>
      apply RegularPrimeDevissage.euler_eq_zero_of_prime_quotients R N (r :: rs) hr hm hi
      intro p hp
      have hdim : Module.supportDim R (R ⧸ p.asIdeal) < ((r :: rs).length : WithBot ℕ∞) :=
        (RegularPrimeDevissage.supportDim_le_of_support_subset R (ModuleCat.of R (R ⧸ p.asIdeal)) N hp).trans_lt hd
      have hip : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩
          Module.support R (R ⧸ p.asIdeal) ⊆ {IsLocalRing.closedPoint R} :=
        (Set.inter_subset_inter_right _ hp).trans hi
      by_cases hd0 : Module.supportDim R (R ⧸ p.asIdeal) ≤ 0
      · exact RegularPrimeDevissage.euler_eq_zero_of_supportDim_nonpos R (ModuleCat.of R (R ⧸ p.asIdeal))
          (r :: rs) hr hm (List.cons_ne_nil _ _) hd0
      obtain ⟨s, he, hrs, hms, hnp, hdrop⟩ := Regular.PrimeEquation.Constructions.exists_regular_head
        R p r rs hr hm (lt_of_not_ge hd0) hip
      let : IsLocalRing (R ⧸ Ideal.span {s}) := Regular.EquationQuotientSupport.Constructions.quotientLocalRing R s (hms s (List.mem_cons_self))
      let : Module.Finite (R ⧸ Ideal.span {s}) (QuotSMulTop s (R ⧸ p.asIdeal)) :=
        Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {s}) _
      let tail := rs.map (algebraMap R (R ⧸ Ideal.span {s}))
      have htail : tail.length = n := by
        simpa only [tail, List.length_map, List.length_cons, Nat.succ.injEq] using hlen
      have hrt : IsWeaklyRegular (R ⧸ Ideal.span {s}) tail := Regular.EquationQuotients.Constructions.weaklyRegular_tail R s rs hrs
      have hmt : ∀ x ∈ tail, x ∈ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {s}) :=
        Regular.EquationQuotientSupport.Constructions.maximalIdeal_tail R s rs (fun x hx => hms x (List.mem_cons_of_mem s hx))
      have hit : PrimeSpectrum.zeroLocus (Ideal.ofList tail : Set (R ⧸ Ideal.span {s})) ∩
          Module.support (R ⧸ Ideal.span {s}) (QuotSMulTop s (R ⧸ p.asIdeal)) ⊆
          {IsLocalRing.closedPoint (R ⧸ Ideal.span {s})} :=
        Regular.EquationQuotientSupport.Constructions.isolated_tail R s (R ⧸ p.asIdeal) rs (by rw [he]; exact hip)
      have hdt : Module.supportDim (R ⧸ Ideal.span {s}) (QuotSMulTop s (R ⧸ p.asIdeal)) <
          (tail.length : WithBot ℕ∞) := by
        rw [Regular.EquationQuotientSupport.Constructions.quotient_supportDim R s (R ⧸ p.asIdeal)]
        simp only [tail, List.length_map]
        apply ENat.WithBot.add_one_le_natCast_iff.mp
        apply hdrop.trans
        apply ENat.WithBot.lt_add_one_iff.mp
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hdim
      have hz := ih (R ⧸ Ideal.span {s}) (ModuleCat.of (R ⧸ Ideal.span {s})
        (QuotSMulTop s (R ⧸ p.asIdeal))) tail htail hrt hmt hdt hit
      let := Regular.QuotientProjectiveDimension.Constructions.bound (R ⧸ Ideal.span {s}) tail hrt hmt
      have heuler := SequenceChangeOfRings.euler_eq R s rs
        (ModuleCat.of R (R ⧸ p.asIdeal)) ((isWeaklyRegular_cons_iff R s rs).mp hrs).1 hnp
        (r :: rs).length
      calc
        _ = Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (s :: rs)))
            (ModuleCat.of R (R ⧸ p.asIdeal)) (r :: rs).length :=
          IsolatedEuler.euler_iso_left R
            (Ideal.quotientEquivAlgOfEq R he.symm).toLinearEquiv.toModuleIso _ _
        _ = Euler.Tor.euler (R ⧸ Ideal.span {s})
            (ModuleCat.of (R ⧸ Ideal.span {s}) ((R ⧸ Ideal.span {s}) ⧸ Ideal.ofList tail))
            (ModuleCat.of (R ⧸ Ideal.span {s}) (QuotSMulTop s (R ⧸ p.asIdeal)))
            (r :: rs).length := heuler
        _ = Euler.Tor.euler (R ⧸ Ideal.span {s})
            (ModuleCat.of (R ⧸ Ideal.span {s}) ((R ⧸ Ideal.span {s}) ⧸ Ideal.ofList tail))
            (ModuleCat.of (R ⧸ Ideal.span {s}) (QuotSMulTop s (R ⧸ p.asIdeal))) tail.length :=
          EulerCutoff.stable_left (R ⧸ Ideal.span {s}) _ _ tail.length
            (r :: rs).length (by simp only [tail, List.length_map, List.length_cons]; omega)
        _ = 0 := hz

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N] (rs : List R)
  (hr : IsWeaklyRegular R rs) (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
  (hd : Module.supportDim R N < (rs.length : WithBot ℕ∞))
  (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R N ⊆
    {IsLocalRing.closedPoint R})

include hr hm hd hi

theorem euler_eq_zero : Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N rs.length = 0 :=
  euler_eq_zero_of_length rs.length R N rs rfl hr hm hd hi

theorem euler_eq_zero_above_length (d : ℕ) (hD : rs.length ≤ d) :
    Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) N d = 0 := by
  let := Regular.QuotientProjectiveDimension.Constructions.bound R rs hr hm
  exact (EulerCutoff.stable_left R _ N rs.length d hD).trans
    (euler_eq_zero R N rs hr hm hd hi)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RegularSequenceVanishing
