import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Polynomial Growth -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth.Constructions.Growth

noncomputable section

/-!
# Polynomial growth in the analytic extension argument for HolomorphicAlgebraicity

Cauchy's estimates force the high Taylor coefficients of an entire function
with polynomial growth to vanish. This provides actual polynomial equations
from holomorphic coefficients in a projection argument.
-/

open Filter Set _root_.Metric
open scoped _root_.Topology BigOperators

/-- Polynomial growth forces every Taylor coefficient above that degree to vanish. -/
theorem iteratedDeriv_zero_of_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} {d n : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d) (hn : d < n) :
    iteratedDeriv n f 0 = 0 := by
  have hlim : Tendsto (fun R : ℝ => (n.factorial : ℝ) * C / R ^ (n - d))
      atTop (𝓝 0) :=
    (tendsto_pow_atTop (Nat.sub_pos_of_lt hn).ne').const_div_atTop _
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb : ‖iteratedDeriv n f 0‖ ≤
      (n.factorial : ℝ) * (C * R ^ d) / R ^ n := by
    apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR0 hf.diffContOnCl
    intro z hz
    have hzR : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    simpa only [hzR, max_eq_right hR] using hbound z
  have hpow : R ^ n = R ^ d * R ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_of_le hn.le]
  refine hb.trans_eq ?_
  rw [hpow]
  field_simp

/-- The finite Taylor polynomial used in the polynomial-growth argument. -/
def taylorPolynomial (f : ℂ → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (d + 1),
    Polynomial.monomial n ((n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)

theorem taylorPolynomial_natDegree_le (f : ℂ → ℂ) (d : ℕ) :
    (taylorPolynomial f d).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hn))

/-- An entire function with growth of order at most `d` is a polynomial of
degree at most `d`, with its coefficients explicitly given by derivatives. -/
theorem eq_taylorPolynomial_of_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} {d : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d) (z : ℂ) :
    (taylorPolynomial f d).eval z = f z := by
  have hvanish (n : ℕ) (hn : n ∉ Finset.range (d + 1)) :
      (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n = 0 := by
    have hdn : d < n := Nat.lt_of_succ_le (by
      simpa only [Finset.mem_range, not_lt] using hn)
    rw [iteratedDeriv_zero_of_growth hf hbound hdn]
    simp
  have hsum : HasSum
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n)
      (∑ n ∈ Finset.range (d + 1),
        (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hTaylor := Complex.hasSum_taylorSeries_of_entire hf 0 z
  have hTaylor' : HasSum
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 * z ^ n) (f z) := by
    simpa only [sub_zero, smul_eq_mul, mul_left_comm, mul_comm, mul_assoc] using hTaylor
  simpa only [taylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    using hsum.unique hTaylor'

theorem exists_polynomial_of_growth
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C : ℝ} {d : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ d ∧ ∀ z, p.eval z = f z :=
  ⟨taylorPolynomial f d, taylorPolynomial_natDegree_le f d,
    eq_taylorPolynomial_of_growth hf hbound⟩

abbrev node (d : ℕ) (i : Fin (d + 1)) : ℂ := i.val

theorem node_injective (d : ℕ) : Function.Injective (node d) := by
  intro i j h
  apply Fin.ext
  exact_mod_cast h

def cardinalBasis (d : ℕ) (i : Fin (d + 1)) : Polynomial ℂ :=
  Lagrange.basis Finset.univ (node d) i

/-- Fixed interpolation nodes recover every univariate polynomial of bounded degree. -/
theorem interpolation_formula {d : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ d) (z : ℂ) :
    p.eval z = ∑ i : Fin (d + 1), p.eval (node d i) * (cardinalBasis d i).eval z := by
  have hdeg : p.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.natDegree_le_iff_degree_le.mp hp).trans_lt (by
      exact_mod_cast Nat.lt_succ_self d)
  have heq := Lagrange.eq_interpolate (node_injective d).injOn hdeg
  have hev := congrArg (Polynomial.eval z) heq
  simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, cardinalBasis] using hev

/-- Splitting off one coordinate keeps polynomial growth, with an explicit constant. -/
theorem growth_cons_bound {n d : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d)
    (c : ℂ) (z : Fin n → ℂ) :
    ‖f (Fin.cons c z)‖ ≤ C * (max 1 ‖c‖) ^ d * (max 1 ‖z‖) ^ d := by
  have hc1 : 1 ≤ max 1 ‖c‖ := le_max_left _ _
  have hz1 : 1 ≤ max 1 ‖z‖ := le_max_left _ _
  have hc0 : 0 ≤ max 1 ‖c‖ := le_trans zero_le_one hc1
  have hz0 : 0 ≤ max 1 ‖z‖ := le_trans zero_le_one hz1
  have hmc : max 1 ‖c‖ ≤ max 1 ‖c‖ * max 1 ‖z‖ := by nlinarith
  have hmz : max 1 ‖z‖ ≤ max 1 ‖c‖ * max 1 ‖z‖ := by nlinarith
  have hnorm : ‖(Fin.cons c z : Fin (n + 1) → ℂ)‖ ≤ max 1 ‖c‖ * max 1 ‖z‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc0 hz0)).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (le_max_right _ _).trans hmc
    · exact (norm_le_pi_norm z j).trans ((le_max_right _ _).trans hmz)
  have hmax : max 1 ‖(Fin.cons c z : Fin (n + 1) → ℂ)‖ ≤
      max 1 ‖c‖ * max 1 ‖z‖ :=
    max_le (hc1.trans hmc) hnorm
  calc
    ‖f (Fin.cons c z)‖ ≤ C * max 1 ‖(Fin.cons c z : Fin (n + 1) → ℂ)‖ ^ d := hbound _
    _ ≤ C * (max 1 ‖c‖ * max 1 ‖z‖) ^ d := by gcongr
    _ = C * (max 1 ‖c‖) ^ d * (max 1 ‖z‖) ^ d := by rw [mul_pow, mul_assoc]

/-- Polynomial growth and holomorphy on every affine complex line suffice to
represent a function by a multivariate polynomial. -/
theorem exists_mvPolynomial_of_line_growth (n : ℕ)
    {f : (Fin n → ℂ) → ℂ}
    (hf : ∀ x v, Differentiable ℂ (fun c : ℂ => f (x + c • v))) {C : ℝ} {d : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z P = f z := by
  induction n generalizing C d with
  | zero =>
      refine ⟨MvPolynomial.C (f 0), ?_⟩
      intro z
      rw [MvPolynomial.eval_C]
      exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
      have hC : 0 ≤ C := by
        have h := hbound 0
        simp only [norm_zero, max_eq_left zero_le_one, one_pow, mul_one] at h
        exact (norm_nonneg _).trans h
      have htail (c : ℂ) : ∃ P : MvPolynomial (Fin n) ℂ,
          ∀ z, MvPolynomial.eval z P = f (Fin.cons c z) := by
        apply ih (C := C * max 1 ‖c‖ ^ d) (d := d) ?_
          (growth_cons_bound hC hbound c)
        intro x v
        convert hf (Fin.cons c x) (Fin.cons 0 v) using 1
        funext a
        congr 1
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      choose P hP using fun i : Fin (d + 1) => htail (node d i)
      refine ⟨∑ i : Fin (d + 1),
        MvPolynomial.rename Fin.succ (P i) * (cardinalBasis d i).toMvPolynomial 0, ?_⟩
      intro z
      have hhead : Differentiable ℂ (fun c => f (Fin.cons c (Fin.tail z))) := by
        convert hf (Fin.cons 0 (Fin.tail z)) (Fin.cons 1 0) using 1
        funext a
        congr 1
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      obtain ⟨q, hqdeg, hq⟩ := exists_polynomial_of_growth hhead
        (C := C * max 1 ‖Fin.tail z‖ ^ d) (d := d) (by
          intro c
          simpa only [mul_right_comm] using growth_cons_bound hC hbound c (Fin.tail z))
      calc
        MvPolynomial.eval z (∑ i : Fin (d + 1),
            MvPolynomial.rename Fin.succ (P i) * (cardinalBasis d i).toMvPolynomial 0) =
            ∑ i : Fin (d + 1), f (Fin.cons (node d i) (Fin.tail z)) *
              (cardinalBasis d i).eval (z 0) := by
          simp only [map_sum, map_mul, MvPolynomial.eval_rename,
            MvPolynomial.eval_toMvPolynomial]
          apply Finset.sum_congr rfl
          intro i _
          change MvPolynomial.eval (Fin.tail z) (P i) * _ = _
          rw [hP i (Fin.tail z)]
        _ = f (Fin.cons (z 0) (Fin.tail z)) := by
          simpa only [hq] using (interpolation_formula q hqdeg (z 0)).symm
        _ = f z := by rw [Fin.cons_self_tail]

/-- An entire function on a finite-dimensional complex coordinate space with
polynomial growth is represented by a multivariate polynomial. -/
theorem exists_mvPolynomial_of_growth (n : ℕ)
    {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f) {C : ℝ} {d : ℕ}
    (hbound : ∀ z, ‖f z‖ ≤ C * (max 1 ‖z‖) ^ d) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z, MvPolynomial.eval z P = f z :=
  exists_mvPolynomial_of_line_growth n
    (fun x v => hf.comp ((differentiable_const x).add
      (differentiable_id.smul_const v))) hbound

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth.Constructions.Growth
