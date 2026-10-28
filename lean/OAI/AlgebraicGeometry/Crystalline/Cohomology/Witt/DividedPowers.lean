import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.DividedPowers.Padic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.Algebra.CharP.Basic

/-! # Divided Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

noncomputable section

/-!
# Cohomology: divided powers on the crystalline coefficient ring

For a perfect field `k` of characteristic `p`, construct divided powers on
`(p) ⊆ W(k)` by proving the integrality of `x^n / n!` in the Witt-vector
fraction field. This is arithmetic infrastructure for the crystalline site;
no cohomology comparison is assumed or asserted here.
-/

variable (p : ℕ) [hp : Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing (WittVector p k)

omit [PerfectRing k p] in
/-- The prime-to-`p` part of a nonzero integer is a unit in `W(k)`. -/
theorem natCast_isUnit_of_not_dvd (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : W) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  change (WittVector.constantCoeff : W →+* k) m ≠ 0
  rw [map_natCast]
  exact (CharP.cast_eq_zero_iff k p m).not.mpr hm

omit [PerfectRing k p] in
/-- Witt vectors of a positive-characteristic field have characteristic zero. -/
instance wittCharZero : CharZero W := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero (R := W)).mpr
  intro q hq
  by_cases heq : p = q
  · subst q
    exact WittVector.p_nonzero p k
  · exact (natCast_isUnit_of_not_dvd p k q
      ((Nat.prime_dvd_prime_iff_eq hp.out hq).not.mpr heq)).ne_zero

omit [PerfectRing k p] in
/-- Factorials have the expected `p`-power part in the Witt ring. -/
theorem factorial_eq_p_pow_mul_unit (n : ℕ) :
    ∃ u : Wˣ, (n.factorial : W) = (p : W) ^ padicValNat p n.factorial * u := by
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    n.factorial_ne_zero p hp.out.ne_one
  have hm0 : m ≠ 0 := by
    intro h
    exact hm (h ▸ dvd_zero p)
  have he : padicValNat p n.factorial = e := by
    rw [hnm, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨u, hu⟩ := natCast_isUnit_of_not_dvd p k m hm
  refine ⟨u, ?_⟩
  rw [he, hu]
  simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun a : ℕ => (a : W)) hnm

omit [PerfectRing k p] in
/-- The factorial denominator can be divided out integrally. For positive
degree the resulting divided power still belongs to `(p)`. -/
theorem factorial_division_integral (n : ℕ) (x : W)
    (hx : x ∈ Ideal.span {(p : W)}) :
    ∃ y : W, (n ≠ 0 → y ∈ Ideal.span {(p : W)}) ∧
      (n.factorial : W) * y = x ^ n := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨u, hu⟩ := factorial_eq_p_pow_mul_unit p k n
  let v := padicValNat p n.factorial
  let y : W := (p : W) ^ (n - v) * z ^ n * (↑(u⁻¹) : W)
  refine ⟨y, ?_, ?_⟩
  · intro hn
    apply Ideal.mem_span_singleton.mpr
    have hv : v < n := padicValNat_factorial_lt_of_ne_zero p hn
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (dvd_pow_self (p : W) (Nat.sub_ne_zero_of_lt hv)) _) _
  · dsimp [y]
    rw [hu]
    have hv : v ≤ n := padicValNat_factorial_le p n
    calc
      (p : W) ^ v * ↑u * ((p : W) ^ (n - v) * z ^ n * ↑(u⁻¹)) =
          (p : W) ^ v * (p : W) ^ (n - v) * z ^ n * (↑u * ↑(u⁻¹)) := by ring
      _ = (p : W) ^ n * z ^ n := by
        rw [Units.mul_inv, mul_one, ← pow_add, Nat.add_sub_of_le hv]
      _ = ((p : W) * z) ^ n := (mul_pow _ _ _).symm

/-- The canonical divided powers on the ideal `(p)` in `W(k)`. -/
def wittDividedPowers : DividedPowers (Ideal.span {(p : W)}) := by
  classical
  refine DividedPowers.ofInjective (Ideal.span {(p : W)}) (⊤ : Ideal K₀)
    (algebraMap W K₀) (IsFractionRing.injective W K₀)
    (DividedPowers.RatAlgebra.dividedPowers (⊤ : Ideal K₀)) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.span_singleton_eq_top, isUnit_iff_ne_zero]
    exact Nat.cast_ne_zero.mpr hp.out.ne_zero
  · intro n x hx
    obtain ⟨y, hy, hxy⟩ := factorial_division_integral p k n x hx
    refine ⟨y, hy, ?_⟩
    simp only [DividedPowers.RatAlgebra.dpow_apply, Submodule.mem_top,
      ite_true, Ring.inverse_eq_inv']
    apply mul_left_cancel₀ (show (n.factorial : K₀) ≠ 0 from
      Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    rw [← mul_assoc, mul_inv_cancel₀
      (show (n.factorial : K₀) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_mul]
    simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap W K₀) hxy

omit [PerfectRing k p] in
/-- In the fraction field, the constructed divided powers are exactly
the usual factorial quotients. -/
theorem algebraMap_dpow (n : ℕ) (x : W) (hx : x ∈ Ideal.span {(p : W)}) :
    algebraMap W K₀ ((wittDividedPowers p k).dpow n x) =
      (algebraMap W K₀ x) ^ n / (n.factorial : K₀) := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr n.factorial_ne_zero)).mpr
  have h := congrArg (algebraMap W K₀)
    ((wittDividedPowers p k).factorial_mul_dpow_eq_pow (n := n) hx)
  simpa only [map_mul, map_natCast, map_pow, mul_comm] using h

/-- Frobenius preserves the divided-power ideal. -/
theorem frobenius_mem (x : W) (hx : x ∈ Ideal.span {(p : W)}) :
    WittVector.frobeniusEquiv p k x ∈ Ideal.span {(p : W)} := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [map_mul, map_natCast]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

/-- The canonical Witt Frobenius respects the canonical divided powers. -/
theorem frobenius_dpow (n : ℕ) (x : W) (hx : x ∈ Ideal.span {(p : W)}) :
    WittVector.frobeniusEquiv p k ((wittDividedPowers p k).dpow n x) =
      (wittDividedPowers p k).dpow n (WittVector.frobeniusEquiv p k x) := by
  apply mul_left_cancel₀ (show (n.factorial : W) ≠ 0 from
    Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  calc
    (n.factorial : W) * WittVector.frobeniusEquiv p k
        ((wittDividedPowers p k).dpow n x) =
      WittVector.frobeniusEquiv p k
        ((n.factorial : W) * (wittDividedPowers p k).dpow n x) := by
          rw [map_mul, map_natCast]
    _ = WittVector.frobeniusEquiv p k (x ^ n) := congrArg
      (WittVector.frobeniusEquiv p k)
      ((wittDividedPowers p k).factorial_mul_dpow_eq_pow hx)
    _ = (WittVector.frobeniusEquiv p k x) ^ n := map_pow _ _ _
    _ = (n.factorial : W) * (wittDividedPowers p k).dpow n
        (WittVector.frobeniusEquiv p k x) :=
      ((wittDividedPowers p k).factorial_mul_dpow_eq_pow (frobenius_mem p k x hx)).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers
