import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Homogeneous Line At -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomogeneousLineAt.Construction.HomogeneousLine

/-! A nonzero homogeneous polynomial has a nonzero value in the chart X₀ = 1. -/

variable {σ K : Type*} [Field K]

theorem eval_scale {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsHomogeneous d)
    (c : K) (v : σ → K) :
    MvPolynomial.eval (fun i => c * v i) p = c ^ d * MvPolynomial.eval v p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support he]
  ring

theorem exists_eval_at_one_ne_zero [Infinite K] {n d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) K} (hp : p.IsHomogeneous d) (h0 : p ≠ 0) :
    ∃ a : Fin n → K, MvPolynomial.eval (Fin.cons 1 a) p ≠ 0 := by
  classical
  by_contra! h
  apply h0
  apply MvPolynomial.funext_set (fun _ => (Set.univ : Set K) \ {0})
    (fun _ => Set.infinite_univ.sdiff (Set.finite_singleton 0))
  intro v hv
  have hv0 : v 0 ≠ 0 := (hv 0 trivial).2
  let a : Fin n → K := fun i => (v 0)⁻¹ * v i.succ
  have he : (fun i => (v 0)⁻¹ * v i) = Fin.cons 1 a := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hv0]
    · rfl
  have hz := eval_scale hp (v 0)⁻¹ v
  rw [he, h a] at hz
  have hz' : MvPolynomial.eval v p = 0 :=
    (mul_eq_zero.mp hz.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hv0))
  simpa using hz'

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomogeneousLineAt.Construction.HomogeneousLine
