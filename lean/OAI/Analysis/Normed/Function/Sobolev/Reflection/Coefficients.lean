import Mathlib

open Polynomial
open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

def reflectionNode {N : ℕ} (j : Fin N) : ℝ := -((j.val : ℝ)+1)

def reflectionCoefficient (N : ℕ) (j : Fin N) : ℝ :=
  (Lagrange.basis Finset.univ reflectionNode j).eval 1

theorem reflectionNode_negative {N : ℕ} (j : Fin N) : reflectionNode j<0 := by
  dsimp [reflectionNode]
  linarith [Nat.cast_nonneg (α:=ℝ) j.val]

theorem reflectionNode_injective (N : ℕ) : Function.Injective (@reflectionNode N) := by
  intro i j hij
  apply Fin.ext
  dsimp [reflectionNode] at hij
  have hc : (i.val:ℝ)=j.val := by linarith
  exact_mod_cast hc

/-- The finite reflection weights match every normal derivative below
the prescribed order. They are actual Lagrange interpolation weights. -/
theorem reflectionCoefficient_moment {N r : ℕ} (hr : r<N) :
    ∑ j : Fin N, reflectionCoefficient N j * reflectionNode j ^ r = 1 := by
  have hinj : Set.InjOn (@reflectionNode N) (Finset.univ : Finset (Fin N)) :=
    (reflectionNode_injective N).injOn
  have hdeg : ((X : ℝ[X])^r).degree < (Finset.univ : Finset (Fin N)).card := by
    rw [Polynomial.degree_X_pow]
    simpa using hr
  have he := congrArg (Polynomial.eval (1:ℝ)) (Lagrange.eq_interpolate hinj hdeg)
  simp only [Polynomial.eval_pow,Polynomial.eval_X,one_pow,Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  simp only [reflectionCoefficient]
  ring

end OAI.Analysis.Normed.Function.Sobolev
