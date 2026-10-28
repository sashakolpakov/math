import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequencePrimeReduction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFiniteSupport

/-! # Sequence Vanishing -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceVanishing

noncomputable section

/-! Native Tor Euler vanishing for a regular sequence longer than a
strictly decreasing support rank. Prime filtrations reduce the proof
to prime quotients, and each parameter step lowers that rank. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

open RingTheory.Sequence OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequencePrimeReduction

def Vanishing (n : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (_hreg : IsRegular R rs) (_hlen : rs.length = n)
    (ρ : PrimeSpectrum R → ℕ) (_hρ : StrictAnti ρ)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (_hbound : ∀ p ∈ Module.support R M, ρ p < n)
    (_hiso : Module.support R M ∩ Module.support R (SequenceModule.quotient R rs) ⊆ {IsLocalRing.closedPoint R}),
    Tor.Euler.euler R M (SequenceModule.quotient R rs) n = 0

theorem vanishing (n : ℕ) : Vanishing.{u} n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R _ _ _ rs hreg hlen ρ hρ M _ hbound hiso
    let : HasProjectiveDimensionLE (SequenceModule.quotient R rs) n := hlen ▸ SequenceModule.projectiveDimension R rs hreg
    obtain ⟨l, ps, hps, hs⟩ := PrimeFiltrationEuler.exists_prime_sum R M (SequenceModule.quotient R rs)
      n (IsLocalRing.closedPoint R) hiso
    rw [hs]
    apply Finset.sum_eq_zero
    intro i _
    let p := ps i
    have hp : ρ p < n := hbound p (hps i (SequencePrimeReduction.prime_mem R p))
    have hi : Module.support R (R ⧸ p.asIdeal) ∩ Module.support R (SequenceModule.quotient R rs) ⊆
        {IsLocalRing.closedPoint R} := (Set.inter_subset_inter_left _ (hps i)).trans hiso
    cases n with
    | zero => omega
    | succ n =>
      by_cases hc : p = IsLocalRing.closedPoint R
      · cases rs with
        | nil => simp at hlen
        | cons r rs =>
          rw [← hlen]
          apply SequenceFiniteSupport.euler_zero R r rs hreg
            (.of R (R ⧸ p.asIdeal)) (IsLocalRing.closedPoint R)
          rw [hc]
          exact SequencePrimeReduction.closed_support R
      · obtain ⟨r, hr, hrp⟩ := SequencePrimeReduction.exists_parameter R rs p hc hi
        let ss := rs.erase r
        have hperm : rs.Perm (r :: ss) := List.perm_cons_erase hr
        have hregular : IsRegular R (r :: ss) := IsLocalRing.isRegular_of_perm hreg hperm
        have hlength : ss.length = n := by have := hperm.length_eq; simp only [List.length_cons] at this; omega
        let e := SequencePrimeReduction.permutationEquiv R rs (r :: ss) hperm
        have hi' : Module.support R (R ⧸ p.asIdeal) ∩ Module.support R (SequenceModule.quotient R (r :: ss)) ⊆
            {IsLocalRing.closedPoint R} := by rw [← e.support_eq]; exact hi
        let S := Parameter.ScalarQuotient.Ring R r
        let Q := Parameter.ScalarQuotient.quotient R r
        let := SequenceReduction.localRing R r ss hregular
        let N : ModuleCat S := Q.obj (.of R (R ⧸ p.asIdeal))
        let : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S (QuotSMulTop r (R ⧸ p.asIdeal))
        let ts := ss.map (Ideal.Quotient.mk (Ideal.span {r}))
        have ht : IsRegular S ts := SequenceReduction.tail_regular R r ss hregular
        have htl : ts.length = n := (List.length_map _).trans hlength
        let ρ' : PrimeSpectrum S → ℕ := fun q => ρ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {r})) q)
        have hρ' : StrictAnti ρ' := Parameter.QuotientSupport.rank_strict R r ρ hρ
        have hb' : ∀ q ∈ Module.support S N, ρ' q < n := by
          intro q hq
          have hdrop := Parameter.QuotientSupport.rank_drop R r ρ hρ p hrp q hq
          change ρ' q < ρ p at hdrop
          omega
        have hiS := Parameter.QuotientSupport.isolated R r (.of R (R ⧸ p.asIdeal))
          (SequenceModule.quotient R (r :: ss)) hi'
        have hi'' : Module.support S N ∩ Module.support S (SequenceModule.quotient S ts) ⊆ {IsLocalRing.closedPoint S} := by
          rw [← (SequenceReduction.tailEquiv R r ss).support_eq]
          exact hiS
        have hz := ih n (Nat.lt_succ_self n) S ts ht htl ρ' hρ' N hb' hi''
        have he := Tor.EulerTransport.iso_right R (.of R (R ⧸ p.asIdeal)) e.toModuleIso (n + 1)
        change Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) (SequenceModule.quotient R rs) (n + 1) = 0
        rw [he]
        have hn : n + 1 = (r :: ss).length := by simp only [List.length_cons, hlength]
        rw [hn, SequenceReduction.euler_length R r ss hregular
          (.of R (R ⧸ p.asIdeal)) (SequencePrimeReduction.prime_regular R p r hrp), hlength]
        exact hz

theorem euler_zero (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (hreg : IsRegular R rs) (ρ : PrimeSpectrum R → ℕ) (hρ : StrictAnti ρ)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hbound : ∀ p ∈ Module.support R M, ρ p < rs.length)
    (hiso : Module.support R M ∩ Module.support R (SequenceModule.quotient R rs) ⊆ {IsLocalRing.closedPoint R}) :
    Tor.Euler.euler R M (SequenceModule.quotient R rs) rs.length = 0 :=
  vanishing rs.length R rs hreg rfl ρ hρ M hbound hiso

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceVanishing
