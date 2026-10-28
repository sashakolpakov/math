import Mathlib

/-! # Frobenius Fixed Lifts -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusFixedLifts

noncomputable section

/-!
# Frobenius-fixed elements lift uniquely through nil ideals

For q a positive power of p, a surjective map of characteristic-p rings with
nil kernel induces an isomorphism on the subrings x^q = x. This supplies the
finite-field constants needed in the tilt.
-/

section Powers

variable {R : Type*} [CommRing R] (q : ℕ)

theorem fixed_pow_iterate {x : R} (hx : x ^ q = x) (n : ℕ) : x ^ q ^ n = x := by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ n ih => rw [pow_succ, pow_mul, ih, hx]

theorem nilpotent_fixed_eq_zero (hq : 1 < q) {x : R} (hx : x ^ q = x)
    (hnil : IsNilpotent x) : x = 0 := by
  obtain ⟨m, hm⟩ := hnil
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt m hq
  exact (fixed_pow_iterate q hx n).symm.trans (pow_eq_zero_of_le hn.le hm)

end Powers

variable (p d : ℕ) [Fact p.Prime]
variable (R : Type*) [CommRing R] [CharP R p]

def fixedSubring : Subring R := (iterateFrobenius R p d).eqLocus (RingHom.id R)

theorem mem_fixedSubring (x : R) : x ∈ fixedSubring p d R ↔ x ^ (p ^ d) = x := Iff.rfl

variable {R}
variable {S : Type*} [CommRing S] [CharP S p]

def fixedMap (f : R →+* S) : fixedSubring p d R →+* fixedSubring p d S where
  toFun x := ⟨f x, by
    change f (x : R) ^ (p ^ d) = f x
    rw [← map_pow]
    exact congrArg f x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f (x : R) y)
  map_mul' x y := Subtype.ext (map_mul f (x : R) y)

variable (hd : 0 < d)
variable (f : R →+* S) (hnil : ∀ x : R, f x = 0 → IsNilpotent x)

include hd hnil

theorem fixedMap_injective : Function.Injective (fixedMap p d f) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply nilpotent_fixed_eq_zero (p ^ d) (one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.ne_of_gt hd))
  · exact (x - y).property
  · apply hnil
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hxy)

theorem fixedMap_surjective (hsurj : Function.Surjective f) :
    Function.Surjective (fixedMap p d f) := by
  intro b
  obtain ⟨a, ha⟩ := hsurj (b : S)
  have hn : IsNilpotent (a ^ (p ^ d) - a) := by
    apply hnil
    rw [map_sub, map_pow, ha]
    exact sub_eq_zero.mpr b.property
  obtain ⟨m, hm⟩ := hn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt m
    (one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.ne_of_gt hd))
  have hz : (a ^ (p ^ d) - a) ^ ((p ^ d) ^ n) = 0 := pow_eq_zero_of_le hn.le hm
  have he : (a ^ (p ^ d) - a) ^ ((p ^ d) ^ n) =
      (a ^ ((p ^ d) ^ n)) ^ (p ^ d) - a ^ ((p ^ d) ^ n) := by
    have h := sub_pow_char_pow (p := p) (a ^ (p ^ d)) a (d * n)
    rw [pow_mul] at h
    exact h.trans (congrArg (fun z : R => z - a ^ ((p ^ d) ^ n))
      ((pow_mul a (p ^ d) ((p ^ d) ^ n)).symm.trans
        ((congrArg (fun m : ℕ => a ^ m) (Nat.mul_comm (p ^ d) ((p ^ d) ^ n))).trans
          (pow_mul a ((p ^ d) ^ n) (p ^ d)))))
  have hfixed : (a ^ ((p ^ d) ^ n)) ^ (p ^ d) = a ^ ((p ^ d) ^ n) :=
    sub_eq_zero.mp (he.symm.trans hz)
  refine ⟨⟨a ^ ((p ^ d) ^ n), hfixed⟩, ?_⟩
  apply Subtype.ext
  change f (a ^ ((p ^ d) ^ n)) = (b : S)
  rw [map_pow, ha]
  exact fixed_pow_iterate (p ^ d) b.property n

def fixedEquiv (hsurj : Function.Surjective f) : fixedSubring p d R ≃+* fixedSubring p d S :=
  RingEquiv.ofBijective (fixedMap p d f)
    ⟨fixedMap_injective p d hd f hnil, fixedMap_surjective p d hd f hnil hsurj⟩

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusFixedLifts
