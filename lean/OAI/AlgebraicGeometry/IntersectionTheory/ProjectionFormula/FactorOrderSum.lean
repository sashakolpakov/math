import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Factor Order Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrderSum

noncomputable section

/-! Restricting a nonzero element of a factorial domain gives the sum
of the orders of its actual prime factors, with their multiplicities. -/

universe u v

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [IsDomain S]
  (φ : R →+* S)

theorem prod (L : Multiset R) (h : ∀ a ∈ L, φ a ≠ 0) :
    Ring.ord S (φ L.prod) = (L.map (fun a => Ring.ord S (φ a))).sum := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a L ih =>
    rw [Multiset.prod_cons, map_mul,
      Ring.ord_mul' S (mem_nonZeroDivisors_of_ne_zero (h a (Multiset.mem_cons_self _ _))),
      ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)), Multiset.map_cons, Multiset.sum_cons]

theorem factors [IsDomain R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (a : R) (ha : a ≠ 0) (hφa : φ a ≠ 0) :
    Ring.ord S (φ a) =
      ((UniqueFactorizationMonoid.normalizedFactors a).map (fun r => Ring.ord S (φ r))).sum := by
  have h (r : R) (hr : r ∈ UniqueFactorizationMonoid.normalizedFactors a) : φ r ≠ 0 := by
    obtain ⟨b, hb⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hr
    intro hz
    apply hφa
    rw [hb, map_mul, hz, zero_mul]
  have he := (UniqueFactorizationMonoid.prod_normalizedFactors ha).map φ.toMonoidHom
  exact (Ring.ord_eq_of_associated he).symm.trans
    (FactorOrderSum.prod R S φ (UniqueFactorizationMonoid.normalizedFactors a) h)

theorem factor_multiset [IsDomain R] [UniqueFactorizationMonoid R]
    (a : R) (ha : a ≠ 0) (hφa : φ a ≠ 0) :
    Ring.ord S (φ a) =
      ((UniqueFactorizationMonoid.factors a).map (fun r => Ring.ord S (φ r))).sum := by
  have h (r : R) (hr : r ∈ UniqueFactorizationMonoid.factors a) : φ r ≠ 0 := by
    obtain ⟨b, hb⟩ := UniqueFactorizationMonoid.dvd_of_mem_factors hr
    intro hz
    apply hφa
    rw [hb, map_mul, hz, zero_mul]
  have he := (UniqueFactorizationMonoid.factors_prod ha).map φ.toMonoidHom
  exact (Ring.ord_eq_of_associated he).symm.trans
    (FactorOrderSum.prod R S φ (UniqueFactorizationMonoid.factors a) h)

theorem rational_prod [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    (L : Multiset R) (h : ∀ a ∈ L, φ a ≠ 0) :
    ((Ring.ord S (φ L.prod)).toNat : ℚ) =
      (L.map (fun a => ((Ring.ord S (φ a)).toNat : ℚ))).sum := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a L ih =>
    have ha := h a (Multiset.mem_cons_self _ _)
    have hL : ∀ b ∈ L, φ b ≠ 0 := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    have hp : φ L.prod ≠ 0 := by
      rw [map_multiset_prod]
      exact Multiset.prod_ne_zero (by
        intro hz
        obtain ⟨b, hb, he⟩ := Multiset.mem_map.mp hz
        exact hL b hb he)
    rw [Multiset.prod_cons, map_mul, Ring.ord_mul' S (mem_nonZeroDivisors_of_ne_zero ha),
      ENat.toNat_add (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))
        (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hp)), Nat.cast_add,
      ih hL, Multiset.map_cons, Multiset.sum_cons]

theorem rational_factors [IsDomain R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    (a : R) (ha : a ≠ 0) (hφa : φ a ≠ 0) :
    ((Ring.ord S (φ a)).toNat : ℚ) =
      ((UniqueFactorizationMonoid.factors a).map (fun r => ((Ring.ord S (φ r)).toNat : ℚ))).sum := by
  have h (r : R) (hr : r ∈ UniqueFactorizationMonoid.factors a) : φ r ≠ 0 := by
    obtain ⟨b, hb⟩ := UniqueFactorizationMonoid.dvd_of_mem_factors hr
    intro hz
    apply hφa
    rw [hb, map_mul, hz, zero_mul]
  have he := (UniqueFactorizationMonoid.factors_prod ha).map φ.toMonoidHom
  exact (congrArg (fun n : ℕ∞ => (n.toNat : ℚ)) (Ring.ord_eq_of_associated he)).symm.trans
    (rational_prod R S φ (UniqueFactorizationMonoid.factors a) h)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FactorOrderSum
