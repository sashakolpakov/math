import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTruncatedGeometric

namespace OAI.Algorithms

/-! Algebraic interfaces for constructing a local CRT factor from node
differences and inverting its constant coefficient. -/

namespace SubexponentialSAT.SubexpLocalFactorAlgebra

open Polynomial
open scoped BigOperators

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

theorem localFactor_eq_product (θ : ι → A) (D : ℕ) (i : ι) :
    TruncatedInverse.localFactor θ D i =
      ∏ j ∈ Finset.univ.erase i, (X + C (θ i - θ j)) ^ D := by
  simp [TruncatedInverse.localFactor, JetCRT.cofactor, JetCRT.nodePower,
    prod_comp, pow_comp, sub_eq_add_neg, add_assoc]

theorem localFactor_coeff_zero (θ : ι → A) (D : ℕ) (i : ι) :
    (TruncatedInverse.localFactor θ D i).coeff 0 =
      ∏ j ∈ Finset.univ.erase i, (θ i - θ j) ^ D := by
  simp only [TruncatedInverse.localFactor, coeff_zero_eq_eval_zero, eval_comp,
    eval_add, eval_X, eval_C, zero_add, JetCRT.cofactor, eval_prod,
    JetCRT.nodePower, eval_pow, eval_sub]

theorem residue_localFactor_coeff_ne_zero {E : Type*} [Field E]
    (ρ : A →+* E) (θ : ι → A)
    (hθ : Function.Injective (fun i => ρ (θ i))) (D : ℕ) (i : ι) :
    ρ ((TruncatedInverse.localFactor θ D i).coeff 0) ≠ 0 := by
  rw [localFactor_coeff_zero, map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [map_pow, map_sub]
  apply pow_ne_zero
  intro h
  have hij := hθ (sub_eq_zero.mp h)
  exact (Finset.mem_erase.mp hj).1 hij.symm

/-- Truncating the local factor retains a nonzero residue at its constant
coefficient. This discharges the input condition of the scalar inverse. -/
theorem residue_truncated_localFactor_coeff_ne_zero {E : Type*} [Field E]
    (ρ : A →+* E) (θ : ι → A)
    (hθ : Function.Injective (fun i => ρ (θ i))) (D : ℕ) (hD : 0 < D) (i : ι) :
    ρ ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0) ≠ 0 := by
  simpa only [Truncation.coeff_trunc, ite_eq_left hD] using
    residue_localFactor_coeff_ne_zero ρ θ hθ D i

end SubexponentialSAT.SubexpLocalFactorAlgebra

end OAI.Algorithms
