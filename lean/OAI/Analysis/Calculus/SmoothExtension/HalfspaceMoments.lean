import OAI.Analysis.Normed.Function.Sobolev.Reflection.Coefficients
import Mathlib.Analysis.SpecificLimits.Basic

/-! Finite triangular moment blocks for a smooth halfspace extension.
The n-th block annihilates every lower normal derivative and has unit
n-th moment. Later blocks can therefore be made arbitrarily small without
changing moments which have already been fixed. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace OAI.Analysis.Calculus.SmoothExtension

def momentNode (n : ℕ) (j : Fin (n+1)) : ℝ := -((j.val : ℝ)+1)

def topMomentWeight (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (Lagrange.basis Finset.univ (momentNode n) j).coeff n

theorem momentNode_neg (n : ℕ) (j : Fin (n+1)) : momentNode n j < 0 := by
  dsimp [momentNode]
  linarith [Nat.cast_nonneg (α := ℝ) j.val]

theorem one_le_abs_momentNode (n : ℕ) (j : Fin (n+1)) : 1 ≤ |momentNode n j| := by
  rw [abs_of_neg (momentNode_neg n j)]
  dsimp [momentNode]
  linarith [Nat.cast_nonneg (α := ℝ) j.val]

theorem momentNode_injective (n : ℕ) : Function.Injective (momentNode n) := by
  intro i j hij
  apply Fin.ext
  dsimp [momentNode] at hij
  have h : (i.val : ℝ) = j.val := by linarith
  exact_mod_cast h

theorem topMomentWeight_moment (n q : ℕ) (hq : q ≤ n) :
    (∑ j : Fin (n+1), topMomentWeight n j * momentNode n j ^ q) =
      if q=n then 1 else 0 := by
  have hinj : Set.InjOn (momentNode n) (Finset.univ : Finset (Fin (n+1))) :=
    (momentNode_injective n).injOn
  have hdeg : ((X : ℝ[X])^q).degree < (Finset.univ : Finset (Fin (n+1))).card := by
    rw [Polynomial.degree_X_pow]
    simpa using (show (q : WithBot ℕ) < n+1 by exact_mod_cast (Nat.lt_succ_of_le hq))
  have he := congrArg (fun p : ℝ[X] => p.coeff n) (Lagrange.eq_interpolate hinj hdeg)
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.eval_pow, Polynomial.eval_X] at he
  simpa [topMomentWeight, Polynomial.coeff_X_pow, eq_comm, mul_comm] using he.symm

def scaledMomentNode (n : ℕ) (R : ℝ) (j : Fin (n+1)) : ℝ := R*momentNode n j

def scaledMomentWeight (n : ℕ) (c R : ℝ) (j : Fin (n+1)) : ℝ :=
  c / R^n * topMomentWeight n j

theorem scaledMomentWeight_moment (n q : ℕ) (hq : q ≤ n)
    (c R : ℝ) (hR : R ≠ 0) :
    (∑ j : Fin (n+1), scaledMomentWeight n c R j * scaledMomentNode n R j ^ q) =
      if q=n then c else 0 := by
  simp only [scaledMomentWeight, scaledMomentNode, mul_pow]
  have he : (∑ j : Fin (n+1), c/R^n*topMomentWeight n j*(R^q*momentNode n j^q)) =
      (c/R^n*R^q) * ∑ j : Fin (n+1), topMomentWeight n j*momentNode n j^q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,topMomentWeight_moment n q hq]
  by_cases hqn : q=n
  · simp only [hqn,ite_true,mul_one]
    field_simp
  · simp [hqn]

theorem scaledMomentWeight_abs_moment (n q : ℕ) (hq : q ≤ n)
    (c R : ℝ) (hR : 0 < R) :
    (∑ j : Fin (n+1), |scaledMomentWeight n c R j| * |scaledMomentNode n R j| ^ q) =
      (|c| * ∑ j : Fin (n+1), |topMomentWeight n j| * |momentNode n j| ^ q) /
        R^(n-q) := by
  simp only [scaledMomentWeight, scaledMomentNode, abs_mul, abs_div, abs_pow,
    abs_of_pos hR]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hn : R^n = R^q * R^(n-q) := by rw [← pow_add, Nat.add_sub_of_le hq]
  rw [hn]
  field_simp
  simp only [mul_pow]
  ring

theorem exists_scale_small_moments (n : ℕ) (c ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ q : ℕ, q < n →
      (∑ j : Fin (n+1), |scaledMomentWeight n c R j| *
        |scaledMomentNode n R j| ^ q) ≤ ε := by
  open Filter in
  have he : ∀ q : Fin n, ∀ᶠ R : ℝ in atTop,
      (∑ j : Fin (n+1), |scaledMomentWeight n c R j| *
        |scaledMomentNode n R j| ^ (q:ℕ)) ≤ ε := by
    intro q
    have ht : Tendsto (fun R : ℝ =>
        (|c| * ∑ j : Fin (n+1), |topMomentWeight n j| *
          |momentNode n j|^(q:ℕ)) / R^(n-(q:ℕ))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0:ℝ)] with R he hR
    rw [scaledMomentWeight_abs_moment n q q.isLt.le c R hR]
    exact he.le
  open Filter in
  obtain ⟨R, hR, h⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (Filter.eventually_all.2 he)).exists
  exact ⟨R,hR,fun q hq => h ⟨q,hq⟩⟩

end OAI.Analysis.Calculus.SmoothExtension
