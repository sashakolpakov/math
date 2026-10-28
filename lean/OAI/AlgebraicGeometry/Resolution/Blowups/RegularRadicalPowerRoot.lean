import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform
import Mathlib.RingTheory.Ideal.Operations

/-! # Regular Radical Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.RegularRadicalPowerRoot.Construction

noncomputable section

/-! Exact root extraction for powers of a regular radical principal ideal. -/

variable {R : Type*} [CommRing R]

/-- Powers detect the exact order along a regular reduced principal divisor. -/
theorem regular_radical_principal_power_root (c : R) (hc : IsRegular c)
    (hrad : (Ideal.span {c}).IsRadical) (m q : ℕ) (hq : 0 < q) (x : R)
    (hx : x ^ q ∈ (Ideal.span {c}) ^ (m * q)) : x ∈ (Ideal.span {c}) ^ m := by
  induction m generalizing x with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      trivial
  | succ m ih =>
      have hxI : x ∈ Ideal.span {c} :=
        hrad ⟨q, (Ideal.pow_le_self (Nat.mul_ne_zero (Nat.succ_ne_zero m) (Nat.ne_of_gt hq))) hx⟩
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hxI
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨z, hz⟩ := hx
      have he : c ^ q * y ^ q = c ^ q * (c ^ (m * q) * z) := by
        calc
          c ^ q * y ^ q = (c * y) ^ q := (mul_pow c y q).symm
          _ = c ^ ((m + 1) * q) * z := hz
          _ = c ^ q * (c ^ (m * q) * z) := by
            rw [Nat.add_mul, Nat.one_mul, pow_add]
            ring
      have hy : y ^ q ∈ (Ideal.span {c}) ^ (m * q) := by
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        exact ⟨z, (hc.pow q).left he⟩
      rw [pow_succ']
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) (ih y hy)

/-- The corresponding ideal containment extracts the prescribed power
without weakening the exponent or assuming a coordinate presentation. -/
theorem regular_radical_principal_ideal_power_root (c : R) (hc : IsRegular c)
    (hrad : (Ideal.span {c}).IsRadical) (J : Ideal R) (m q : ℕ) (hq : 0 < q)
    (hJ : J ^ q ≤ (Ideal.span {c}) ^ (m * q)) : J ≤ (Ideal.span {c}) ^ m := by
  intro x hx
  exact regular_radical_principal_power_root c hc hrad m q hq x (hJ (Ideal.pow_mem_pow hx q))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.RegularRadicalPowerRoot.Construction
