import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtalePowers
import Mathlib.Algebra.Polynomial.Lifts

/-! # Standard Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLift

noncomputable section

/-! Lift actual standard etale presentations along any surjective coefficient map. -/

open _root_.Polynomial

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  (q : R →+* S) (hq : Function.Surjective q) (P : StandardEtalePair S)

include hq in
theorem exists_pair : ∃ Q : StandardEtalePair R, ∃ n : ℕ,
    (Q.map q).f = P.f ∧ (Q.map q).g = P.g ^ (n + 1) := by
  obtain ⟨a, b, n, h⟩ := P.cond
  have hsurj := Polynomial.map_surjective q hq
  obtain ⟨F, hF, _, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts P.f).mpr (hsurj P.f)) P.monic_f
  obtain ⟨G, hG⟩ := hsurj P.g
  obtain ⟨A, hA⟩ := hsurj a
  obtain ⟨B, hB⟩ := hsurj b
  let Q : StandardEtalePair R :=
    { f := F
      monic_f := hmonic
      g := G * (F.derivative * A + F * B)
      cond := ⟨G * A, G * B, 1, by rw [pow_one]; ring⟩ }
  refine ⟨Q, n, hF, ?_⟩
  change Polynomial.map q (G * (F.derivative * A + F * B)) = P.g ^ (n + 1)
  rw [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    ← Polynomial.derivative_map, hF, hG, hA, hB, h, pow_succ']

def pair : StandardEtalePair R := (exists_pair q hq P).choose

def exponent : ℕ := (exists_pair q hq P).choose_spec.choose

theorem pair_f : ((pair q hq P).map q).f = P.f :=
  (exists_pair q hq P).choose_spec.choose_spec.1

theorem pair_g : ((pair q hq P).map q).g = P.g ^ (exponent q hq P + 1) :=
  (exists_pair q hq P).choose_spec.choose_spec.2

def residueEquiv : ((pair q hq P).map q).Ring ≃ₐ[S] P.Ring :=
  StandardEtalePowers.equiv P ((pair q hq P).map q) (exponent q hq P)
    (pair_f q hq P) (pair_g q hq P)

theorem residueEquiv_X : residueEquiv q hq P ((pair q hq P).map q).X = P.X :=
  StandardEtalePowers.equiv_X P ((pair q hq P).map q) (exponent q hq P)
    (pair_f q hq P) (pair_g q hq P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLift
