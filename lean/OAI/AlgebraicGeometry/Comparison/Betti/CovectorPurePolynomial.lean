import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Covector Pure Polynomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CovectorPurePolynomial.Holomorphic

noncomputable section

section

/-! Polynomial continuation of simultaneous complex scaling of real multilinear covectors. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}
  (ω : MultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : Fin n → E)

def covectorScalarPolynomial : Polynomial ℂ :=
  ∑ s : Finset (Fin n), Polynomial.C (ω (s.piecewise (fun i => Complex.I • v i) v)) *
    Polynomial.X ^ s.card

omit [IsScalarTower ℝ ℂ E] in
theorem covector_piecewise_scale (s : Finset (Fin n)) (t : ℝ) :
    ω (s.piecewise (fun i => t • (Complex.I • v i)) v) =
      (t : ℂ) ^ s.card * ω (s.piecewise (fun i => Complex.I • v i) v) := by
  have hv : s.piecewise (fun i => t • (Complex.I • v i)) v =
      fun i => (if i ∈ s then t else 1) • (s.piecewise (fun j => Complex.I • v j) v i) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hv, ω.map_smul_univ]
  simp only [Fintype.prod_ite_mem, Finset.prod_const, Complex.real_smul, Complex.ofReal_pow]

theorem covectorScalarPolynomial_eval_real (t : ℝ) :
    (covectorScalarPolynomial ω v).eval (t : ℂ) =
      ω (fun i => ((1 : ℂ) + (t : ℂ) * Complex.I) • v i) := by
  have hv : (fun i => ((1 : ℂ) + (t : ℂ) * Complex.I) • v i) =
      (fun i => t • (Complex.I • v i)) + v := by
    funext i
    have hs (w : E) : (t : ℂ) • w = t • w := algebraMap_smul ℂ t w
    simp only [add_smul, one_smul, mul_smul, Pi.add_apply, hs, add_comm]
  rw [hv, ω.map_add_univ]
  simp only [covectorScalarPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro s _
  rw [covector_piecewise_scale, mul_comm]

end

section

/-! The highest complex-scaling character determines the full covector scalar polynomial. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}
  (ω : MultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : Fin n → E)

theorem covectorScalarPolynomial_eq_of_homogeneous
    (hω : ∀ z : ℂˣ, ω (fun i => (z : ℂ) • v i) = (z : ℂ) ^ n * ω v) :
    covectorScalarPolynomial ω v =
      (Polynomial.C 1 + Polynomial.C Complex.I * Polynomial.X) ^ n * Polynomial.C (ω v) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro z ⟨t, rfl⟩
  change (covectorScalarPolynomial ω v).eval (t : ℂ) = _
  rw [covectorScalarPolynomial_eval_real]
  have ht : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  have h := hω (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) ht)
  simpa only [Units.val_mk0, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, mul_comm] using h

theorem covector_complex_projection_identity
    (hω : ∀ z : ℂˣ, ω (fun i => (z : ℂ) • v i) = (z : ℂ) ^ n * ω v) :
    ∑ s : Finset (Fin n), (-Complex.I) ^ s.card *
        ω (s.piecewise (fun i => Complex.I • v i) v) = (2 : ℂ) ^ n * ω v := by
  have h := congrArg (Polynomial.eval (-Complex.I))
    (covectorScalarPolynomial_eq_of_homogeneous ω v hω)
  simp only [covectorScalarPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add] at h
  have hb : (1 : ℂ) + Complex.I * (-Complex.I) = 2 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  rw [hb] at h
  calc
    _ = ∑ s : Finset (Fin n), ω (s.piecewise (fun i => Complex.I • v i) v) *
        (-Complex.I) ^ s.card := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ = _ := h

end

/-! Pairing subsets isolates complex linearity in one argument of a real covector. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {n : ℕ} (ω : MultilinearMap ℝ (fun _ : Fin n => E) ℂ) (v : Fin n → E)

def covectorProjectionTerm (s : Finset (Fin n)) : ℂ :=
  (-Complex.I) ^ s.card * ω (s.piecewise (fun i => Complex.I • v i) v)

theorem covectorProjectionTerm_pair (s : Finset (Fin n)) (k : Fin n) (hk : k ∉ s) :
    covectorProjectionTerm ω (Function.update v k (Complex.I • v k)) s +
        covectorProjectionTerm ω (Function.update v k (Complex.I • v k)) (insert k s) =
      Complex.I * (covectorProjectionTerm ω v s + covectorProjectionTerm ω v (insert k s)) := by
  let w := s.piecewise (fun i => Complex.I • v i) v
  have h0 : w k = v k := by simp [w, hk]
  have h1 : s.piecewise
      (fun i => Complex.I • Function.update v k (Complex.I • v k) i)
      (Function.update v k (Complex.I • v k)) = Function.update w k (Complex.I • v k) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp [w, Finset.piecewise, hk]
    · simp [w, Finset.piecewise, hj]
  have h2 : (insert k s).piecewise (fun i => Complex.I • v i) v =
      Function.update w k (Complex.I • v k) := by
    exact Finset.piecewise_insert s (fun i => Complex.I • v i) v k
  have h3 : (insert k s).piecewise
      (fun i => Complex.I • Function.update v k (Complex.I • v k) i)
      (Function.update v k (Complex.I • v k)) = Function.update w k (-v k) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp [Finset.piecewise, ← mul_smul]
    · simp [w, Finset.piecewise, hj]
  have hm : ω (Function.update w k (-v k)) = -ω w := by
    rw [ω.map_update_neg, ← h0, Function.update_eq_self]
  change (-Complex.I) ^ s.card * ω _ + (-Complex.I) ^ (insert k s).card * ω _ =
    Complex.I * ((-Complex.I) ^ s.card * ω w + (-Complex.I) ^ (insert k s).card * ω _)
  rw [h1, h2, h3, hm, Finset.card_insert_of_notMem hk, pow_succ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.CovectorPurePolynomial.Holomorphic
