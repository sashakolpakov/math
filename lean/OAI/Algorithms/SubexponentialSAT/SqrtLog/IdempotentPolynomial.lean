import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentCore

namespace OAI.Algorithms

/-! Bounded normal forms for the Newton lift.  The quotient by `H ^ t`
is the univariate presentation of `R[Z,X]/(Z^t,H(X)-Z)`.
All reductions below are monic polynomial division. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev LiftAlgebra (H : R[X]) (t : ℕ) := LiftRing.Extension (H ^ t)

noncomputable def finiteCoordinates (H : R[X]) (hH : H.Monic) (t : ℕ) :
    LiftAlgebra H t ≃ₗ[R] (Fin ((H ^ t).natDegree) → R) :=
  LiftRing.coordinates (hH.pow t)

theorem coordinate_length (H : R[X]) (hH : H.Monic) (t : ℕ) :
    (H ^ t).natDegree = t * H.natDegree := hH.natDegree_pow t

theorem finiteAlgebra_card (H : R[X]) (hH : H.Monic) (t : ℕ) :
    Nat.card (LiftAlgebra H t) = Nat.card R ^ (t * H.natDegree) := by
  rw [LiftRing.natCard_extension (hH.pow t), hH.natDegree_pow]

noncomputable def normalized (F e : R[X]) : ℕ → R[X]
  | 0 => e %ₘ F
  | n + 1 => newton (normalized F e n) %ₘ F

theorem normalized_degree (F e : R[X]) (hF : F.Monic) [Nontrivial R] (n : ℕ) :
    (normalized F e n).degree < F.degree := by
  cases n <;> exact degree_modByMonic_lt _ hF

theorem eval_normalized (F e : R[X]) (_hF : F.Monic)
    (φ : R →+* S) (x : S) (hx : F.eval₂ φ x = 0) (n : ℕ) :
    (normalized F e n).eval₂ φ x = iterate (e.eval₂ φ x) n := by
  induction n with
  | zero => exact eval₂_modByMonic_eq_self_of_root hx
  | succ n ih =>
      change (newton (normalized F e n) %ₘ F).eval₂ φ x = _
      rw [eval₂_modByMonic_eq_self_of_root hx]
      change (eval₂RingHom φ x) (newton (normalized F e n)) = _
      rw [map_newton]
      change newton ((normalized F e n).eval₂ φ x) = _
      rw [ih]
      rfl

noncomputable def quotientAfter (H f : R[X]) : ℕ → R[X]
  | 0 => f
  | n + 1 => quotientAfter H f n /ₘ H

noncomputable def digit (H f : R[X]) (n : ℕ) : R[X] :=
  quotientAfter H f n %ₘ H

theorem digit_natDegree_lt (H f : R[X]) (hH : H.Monic) (hH1 : H ≠ 1) (n : ℕ) :
    (digit H f n).natDegree < H.natDegree :=
  natDegree_modByMonic_lt _ hH hH1

theorem expansion (H f : R[X]) (t : ℕ) :
    f = (∑ s ∈ Finset.range t, digit H f s * H ^ s) + H ^ t * quotientAfter H f t := by
  induction t with
  | zero => simp [quotientAfter]
  | succ t ih =>
      have hdiv := modByMonic_add_div (quotientAfter H f t) H
      calc
        f = (∑ s ∈ Finset.range t, digit H f s * H ^ s) +
            H ^ t * quotientAfter H f t := ih
        _ = _ := by
          rw [Finset.sum_range_succ, quotientAfter, pow_succ]
          dsimp only [digit]
          linear_combination -(H ^ t) * hdiv

theorem eval_expansion (H f : R[X]) (t : ℕ)
    (φ : R →+* S) (x : S) (hx : (H.eval₂ φ x) ^ t = 0) :
    f.eval₂ φ x = ∑ s ∈ Finset.range t, (digit H f s).eval₂ φ x * (H.eval₂ φ x) ^ s := by
  conv_lhs => rw [expansion H f t]
  simp only [eval₂_add, eval₂_finsetSum, eval₂_mul, eval₂_pow, hx, zero_mul, add_zero]

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
