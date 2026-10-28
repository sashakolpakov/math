import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # Polynomial Multiplicative Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialMultiplicativeOrder.Construction

noncomputable section

/-! Exact multiplicativity of polynomial point order, using the initial term of a power series. -/

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Polynomial order at a point, allowing infinite order for the zero polynomial. -/
def polynomialOrderAt (x : σ → R) (p : MvPolynomial σ R) : ℕ∞ :=
  ((PolynomialTranslation.Construction.polynomialTranslate x p : MvPolynomial σ R) : MvPowerSeries σ R).order

/-- Power containment in the point ideal is exactly a lower bound on this order. -/
theorem polynomial_mem_point_pow_iff_order (x : σ → R) (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n ↔ (n : ℕ∞) ≤ polynomialOrderAt x p := by
  rw [← PolynomialTranslation.Construction.polynomialTranslate_mem_vars_pow_iff, mem_pow_idealOfVars_iff']
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro d hd
    exact h d hd
  · intro h d hd
    have hdn : ((Finsupp.degree d : ℕ) : ℕ∞) < n := by exact_mod_cast hd
    exact MvPowerSeries.coeff_of_lt_order (hdn.trans_le h)

/-- Exact finite power containment characterizes the polynomial order. -/
theorem polynomialOrderAt_eq_iff (x : σ → R) (p : MvPolynomial σ R) (n : ℕ) :
    polynomialOrderAt x p = n ↔
      p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ n ∧ p ∉ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 1) := by
  constructor
  · intro h
    refine ⟨(polynomial_mem_point_pow_iff_order x p n).mpr h.ge, ?_⟩
    intro hpow
    have hb := (polynomial_mem_point_pow_iff_order x p (n + 1)).mp hpow
    rw [h] at hb
    have hnat : n + 1 ≤ n := by exact_mod_cast hb
    omega
  · rintro ⟨hlo, hhi⟩
    have hlo' := (polynomial_mem_point_pow_iff_order x p n).mp hlo
    have hhi' : polynomialOrderAt x p < (n + 1 : ℕ) :=
      lt_of_not_ge (fun h => hhi ((polynomial_mem_point_pow_iff_order x p (n + 1)).mpr h))
    rw [Nat.cast_add, Nat.cast_one] at hhi'
    exact le_antisymm ((ENat.lt_add_one_iff (ENat.natCast_ne_top n)).mp hhi') hlo'

variable [IsDomain R]

/-- Orders add under multiplication over an integral coefficient ring. -/
theorem polynomialOrderAt_mul (x : σ → R) (p q : MvPolynomial σ R) :
    polynomialOrderAt x (p * q) = polynomialOrderAt x p + polynomialOrderAt x q := by
  simp only [polynomialOrderAt, map_mul, MvPolynomial.coe_mul, MvPowerSeries.order_mul]

/-- Exact finite polynomial orders add under multiplication. -/
theorem polynomial_point_exact_order_mul (x : σ → R) (p q : MvPolynomial σ R) (a b : ℕ)
    (hp : p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ a) (hp1 : p ∉ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (a + 1))
    (hq : q ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ b) (hq1 : q ∉ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (b + 1)) :
    p * q ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (a + b) ∧ p * q ∉ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (a + b + 1) := by
  apply (polynomialOrderAt_eq_iff x (p * q) (a + b)).mp
  rw [polynomialOrderAt_mul, (polynomialOrderAt_eq_iff x p a).mpr ⟨hp, hp1⟩,
    (polynomialOrderAt_eq_iff x q b).mpr ⟨hq, hq1⟩, Nat.cast_add]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialMultiplicativeOrder.Construction
