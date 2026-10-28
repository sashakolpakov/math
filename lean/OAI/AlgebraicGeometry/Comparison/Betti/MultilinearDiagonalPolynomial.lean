import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Basic.Complex.Basic

/-! # Multilinear Diagonal Polynomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MultilinearDiagonalPolynomial.Dolbeault

noncomputable section

/-! The diagonal of a multilinear form on a finite coordinate space is a homogeneous polynomial. -/

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def multilinearDiagonalPolynomial (n : ℕ) (T : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) :
    MvPolynomial ι ℂ :=
  ∑ v : Fin n → ι, MvPolynomial.C (T (fun k => Pi.single (v k) 1)) *
    ∏ k : Fin n, MvPolynomial.X (v k)

theorem multilinearDiagonalPolynomial_eval (n : ℕ)
    (T : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (multilinearDiagonalPolynomial n T) = T (fun _ => x) := by
  have hx : (∑ i : ι, x i • Pi.single i (1 : ℂ)) = x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have ht := T.map_sum (fun _ : Fin n => fun i : ι => x i • Pi.single i (1 : ℂ))
  have he : (fun _ : Fin n => ∑ i : ι, x i • Pi.single i (1 : ℂ)) = fun _ : Fin n => x :=
    funext (fun _ => hx)
  rw [he] at ht
  rw [multilinearDiagonalPolynomial, map_sum, ht]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, MvPolynomial.eval_C, map_prod]
  simp only [MvPolynomial.eval_X]
  rw [T.map_smul_univ, smul_eq_mul, mul_comm]

theorem multilinearDiagonalPolynomial_homogeneous (n : ℕ)
    (T : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) :
    (multilinearDiagonalPolynomial n T).IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.sum
  intro v _
  apply MvPolynomial.IsHomogeneous.C_mul
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun k => MvPolynomial.X (v k) : Fin n → MvPolynomial ι ℂ) (fun _ => 1)
    (fun k _ => MvPolynomial.isHomogeneous_X ℂ (v k))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_id] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.MultilinearDiagonalPolynomial.Dolbeault
