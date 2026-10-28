import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence
import Mathlib.Algebra.Ring.GeomSum

/-! # Logarithm -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.Logarithm

noncomputable section

/-! A finite integral divided-power logarithm. If a factorial vanishes
in the coefficient ring, its differential is the logarithmic
differential of `1+x`. This compares genuine PD differential forms
without dividing by any integer. -/

open scoped BigOperators

universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
  (I : Ideal A) (δ : DividedPowers I)

def logarithm (N : ℕ) (x : A) : A :=
  ∑ j ∈ Finset.range N, ((-1 : A) ^ j * (j.factorial : A)) * δ.dpow (j + 1) x

variable (D : Derivation R A M)

theorem derivative_logarithm (N : ℕ) {x : A} (hx : x ∈ I)
    (hD : ∀ j, D (δ.dpow (j + 1) x) = δ.dpow j x • D x) :
    D (logarithm I δ N x) = (∑ j ∈ Finset.range N, (-x) ^ j) • D x := by
  rw [logarithm, map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  have hc : D ((-1 : A) ^ j * (j.factorial : A)) = 0 := by simp
  rw [D.leibniz, hc, smul_zero, add_zero, hD, smul_smul]
  congr 1
  rw [mul_assoc, δ.factorial_mul_dpow_eq_pow hx]
  exact (neg_pow x j).symm

include δ in
theorem geometricInverse (N : ℕ) {x : A} (hx : x ∈ I)
    (hN : (N.factorial : A) = 0) :
    (∑ j ∈ Finset.range N, (-x) ^ j) * (1 + x) = 1 := by
  have hxN : x ^ N = 0 := by
    rw [← δ.factorial_mul_dpow_eq_pow hx, hN, zero_mul]
  have hn : (-x) ^ N = 0 := by rw [neg_pow, hxN, mul_zero]
  simpa only [sub_neg_eq_add, hn, sub_zero] using
    (geom_sum_mul_neg (-x) N)

def dlog (u : Aˣ) : M := (↑u⁻¹ : A) • D (u : A)

theorem derivative_logarithm_unit (N : ℕ) (u : Aˣ)
    (hu : (u : A) - 1 ∈ I) (hN : (N.factorial : A) = 0)
    (hD : ∀ j, D (δ.dpow (j + 1) ((u : A) - 1)) =
      δ.dpow j ((u : A) - 1) • D ((u : A) - 1)) :
    D (logarithm I δ N ((u : A) - 1)) = dlog D u := by
  rw [derivative_logarithm I δ D N hu hD]
  have hi := geometricInverse I δ N hu hN
  rw [show 1 + ((u : A) - 1) = (u : A) by ring] at hi
  have he : (∑ j ∈ Finset.range N, (-((u : A) - 1)) ^ j) = (↑u⁻¹ : A) := by
    calc
      _ = ((∑ j ∈ Finset.range N, (-((u : A) - 1)) ^ j) * (u : A)) * ↑u⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hi, one_mul]
  rw [he, map_sub, D.map_one_eq_zero, sub_zero]
  rfl

theorem dlog_mul (u v : Aˣ) : dlog D (u * v) = dlog D u + dlog D v := by
  simp only [dlog, mul_inv_rev, Units.val_mul, D.leibniz, smul_add, smul_smul]
  rw [show (↑v⁻¹ : A) * ↑u⁻¹ * ↑u = ↑v⁻¹ by simp [mul_assoc],
    show (↑v⁻¹ : A) * ↑u⁻¹ * ↑v = ↑u⁻¹ by
      rw [mul_right_comm, Units.inv_mul, one_mul], add_comm]

theorem dlog_one : dlog D (1 : Aˣ) = 0 := by simp [dlog]

theorem dlog_inv (u : Aˣ) : dlog D u⁻¹ = -dlog D u := by
  have h := dlog_mul D u u⁻¹
  rw [mul_inv_cancel, dlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem dlog_sub_exact (N : ℕ) (u v : Aˣ)
    (huv : (↑(v * u⁻¹) : A) - 1 ∈ I) (hN : (N.factorial : A) = 0)
    (hD : ∀ j, D (δ.dpow (j + 1) ((↑(v * u⁻¹) : A) - 1)) =
      δ.dpow j ((↑(v * u⁻¹) : A) - 1) • D ((↑(v * u⁻¹) : A) - 1)) :
    dlog D v - dlog D u =
      D (logarithm I δ N ((↑(v * u⁻¹) : A) - 1)) := by
  rw [derivative_logarithm_unit I δ D N (v * u⁻¹) huv hN hD,
    dlog_mul, dlog_inv, sub_eq_add_neg]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.Logarithm
