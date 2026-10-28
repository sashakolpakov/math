import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton
import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitPolynomial
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Family Orbit Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyOrbitPolynomial.Family

noncomputable section

/-! The top coefficient of a finite tensor orbit is polynomial in any
polynomial family of natural tensor exponents. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyNewton.Family OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitPolynomial _root_.Polynomial

theorem map_boxSum {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) {r : ℕ} (b : Fin r → ℕ) (c : (Fin r → ℕ) → M) :
    f (FamilyNewton.Family.boxSum b c) = FamilyNewton.Family.boxSum b (fun n => f (c n)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change f (∑ i ∈ Finset.range (b 0), _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => ih _ _)

theorem ringHom_boxSum {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) {r : ℕ} (b : Fin r → ℕ) (c : (Fin r → ℕ) → R) :
    f (FamilyNewton.Family.boxSum b c) = FamilyNewton.Family.boxSum b (fun n => f (c n)) :=
  map_boxSum f.toAddMonoidHom b c

theorem boxSum_natDegree {r : ℕ} (b : Fin r → ℕ) (c : (Fin r → ℕ) → Polynomial ℚ)
    (d : ℕ) (h : ∀ n, (c n).natDegree ≤ d) : (FamilyNewton.Family.boxSum b c).natDegree ≤ d := by
  induction r with
  | zero => exact h _
  | succ r ih =>
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact ih _ _ (fun n => h (Fin.cons i n))

theorem boxSum_totalDegree {σ : Type*} {r : ℕ} (b : Fin r → ℕ)
    (c : (Fin r → ℕ) → MvPolynomial σ ℚ) (d : ℕ)
    (h : ∀ n, (c n).totalDegree ≤ d) : (FamilyNewton.Family.boxSum b c).totalDegree ≤ d := by
  induction r with
  | zero => exact h _
  | succ r ih =>
    apply (MvPolynomial.totalDegree_finsetSum _ _).trans
    apply Finset.sup_le
    intro i _
    exact ih _ _ (fun n => h (Fin.cons i n))

def chooseProduct {r : ℕ} (a : Fin r → ℚ) (n : Fin r → ℕ) : Polynomial ℚ :=
  ∏ i, MixedOrbitPolynomial.scaledChoose (a i) (n i)

theorem chooseProduct_natDegree {r : ℕ} (a : Fin r → ℚ) (n : Fin r → ℕ) :
    (chooseProduct a n).natDegree ≤ ∑ i, n i :=
  (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun _i _ => MixedOrbitPolynomial.scaledChoose_natDegree _ _))

theorem chooseProduct_coeff {r : ℕ} (a : Fin r → ℚ) (n : Fin r → ℕ) :
    (chooseProduct a n).coeff (∑ i, n i) = ∏ i, (a i ^ n i / (n i).factorial) := by
  induction r with
  | zero => simp [chooseProduct]
  | succ r ih =>
    change (∏ i : Fin (r + 1), MixedOrbitPolynomial.scaledChoose (a i) (n i)).coeff _ = _
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_succ]
    change (MixedOrbitPolynomial.scaledChoose (a 0) (n 0) * chooseProduct (fun i : Fin r => a i.succ)
      (fun i => n i.succ)).coeff (n 0 + ∑ i : Fin r, n i.succ) = _
    rw [coeff_mul_add_eq_of_natDegree_le (MixedOrbitPolynomial.scaledChoose_natDegree _ _) (chooseProduct_natDegree _ _)]
    rw [MixedOrbitPolynomial.scaledChoose_coeff]
    congr 1
    exact ih _ _

theorem chooseProduct_eval {r : ℕ} (a n : Fin r → ℕ) (m : ℕ) :
    (chooseProduct (fun i => (a i : ℚ)) n).eval (m : ℚ) =
      FamilyNewton.Family.weight (fun i => a i * m) n := by
  simp only [chooseProduct, eval_prod, MixedOrbitPolynomial.scaledChoose_eval, FamilyNewton.Family.weight]

def term {r : ℕ} (c : (Fin r → ℕ) → ℚ) (a : Fin r → ℚ) (n : Fin r → ℕ) : Polynomial ℚ :=
  C (c n) * chooseProduct a n

theorem term_natDegree {r : ℕ} (c : (Fin r → ℕ) → ℚ) (a : Fin r → ℚ) (n : Fin r → ℕ) :
    (term c a n).natDegree ≤ ∑ i, n i :=
  (natDegree_C_mul_le _ _).trans (chooseProduct_natDegree a n)

theorem term_coeff {r : ℕ} (c : (Fin r → ℕ) → ℚ) (a : Fin r → ℚ) (n : Fin r → ℕ) :
    (term c a n).coeff (∑ i, n i) = (c n / ∏ i, ((n i).factorial : ℚ)) * ∏ i, a i ^ n i := by
  rw [term, coeff_C_mul, chooseProduct_coeff, Finset.prod_div_distrib]
  ring

def orbitPolynomial {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d : ℕ) (a : Fin r → ℚ) : Polynomial ℚ :=
  FamilyNewton.Family.boxSum (fun _ => d + 1) (term c a)

theorem orbitPolynomial_natDegree {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d : ℕ)
    (hc : ∀ n, d < ∑ i, n i → c n = 0) (a : Fin r → ℚ) :
    (orbitPolynomial c d a).natDegree ≤ d := by
  apply boxSum_natDegree
  intro n
  by_cases h : ∑ i, n i ≤ d
  · exact (term_natDegree c a n).trans h
  · simp [term, hc n (Nat.lt_of_not_ge h)]

theorem orbitPolynomial_eval {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d : ℕ)
    (a : Fin r → ℕ) (m : ℕ) :
    (orbitPolynomial c d (fun i => (a i : ℚ))).eval (m : ℚ) =
      FamilyNewton.Family.boxSum (fun _ => d + 1) (fun n => FamilyNewton.Family.weight (fun i => a i * m) n * c n) := by
  change (evalRingHom (m : ℚ)).toAddMonoidHom (FamilyNewton.Family.boxSum (fun _ => d + 1)
    (term c (fun i => (a i : ℚ)))) = _
  rw [map_boxSum]
  apply FamilyNewton.Family.boxSum_congr
  intro n
  change (term c (fun i => (a i : ℚ)) n).eval (m : ℚ) = _
  rw [term, eval_mul, eval_C, chooseProduct_eval, mul_comm]

def topPolynomial {σ : Type*} {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d : ℕ)
    (E : Fin r → MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  FamilyNewton.Family.boxSum (fun _ => d + 1) (fun n => if ∑ i, n i = d then
    MvPolynomial.C (c n / ∏ i, ((n i).factorial : ℚ)) * ∏ i, E i ^ n i else 0)

theorem topPolynomial_totalDegree {σ : Type*} {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d b : ℕ)
    (E : Fin r → MvPolynomial σ ℚ) (hE : ∀ i, (E i).totalDegree ≤ b) :
    (topPolynomial c d E).totalDegree ≤ b * d := by
  apply boxSum_totalDegree
  intro n
  split_ifs with hn
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      ∑ i, (E i ^ n i).totalDegree ≤ ∑ i, n i * b :=
        Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hE i)))
      _ = b * d := by rw [← Finset.sum_mul, hn, Nat.mul_comm]
  · simp

theorem topPolynomial_eval {σ : Type*} {r : ℕ} (c : (Fin r → ℕ) → ℚ) (d : ℕ)
    (hc : ∀ n, d < ∑ i, n i → c n = 0)
    (E : Fin r → MvPolynomial σ ℚ) (a : σ → ℚ) :
    (orbitPolynomial c d (fun i => MvPolynomial.eval a (E i))).coeff d =
      MvPolynomial.eval a (topPolynomial c d E) := by
  change (lcoeff ℚ d).toAddMonoidHom (FamilyNewton.Family.boxSum (fun _ => d + 1)
    (term c (fun i => MvPolynomial.eval a (E i)))) = _
  rw [map_boxSum]
  rw [topPolynomial, ringHom_boxSum]
  apply FamilyNewton.Family.boxSum_congr
  intro n
  change (term c (fun i => MvPolynomial.eval a (E i)) n).coeff d = _
  by_cases hn : ∑ i, n i = d
  · rw [ite_eq_left hn, ← hn, term_coeff]
    simp
  · rw [ite_eq_right hn, map_zero]
    by_cases hlt : ∑ i, n i < d
    · exact coeff_eq_zero_of_natDegree_lt ((term_natDegree _ _ _).trans_lt hlt)
    · simp [term, hc n (by omega)]

theorem orbit_polynomials {G : Type*} [AddCommGroup G] {σ : Type*} {r : ℕ}
    (T : Fin r → AddMonoid.End G) (φ : G →+ ℚ) (x : G) (d b : ℕ)
    (hzero : ∀ n : Fin r → ℕ, d < ∑ i, n i → FamilyNewton.Family.ordered (fun i => T i - 1) n x = 0)
    (E : Fin r → MvPolynomial σ ℚ) (hE : ∀ i, (E i).totalDegree ≤ b)
    (e : (σ → ℕ) → Fin r → ℕ)
    (he : ∀ a i, MvPolynomial.eval (fun j => (a j : ℚ)) (E i) = (e a i : ℚ)) :
    ∃ (P : (σ → ℕ) → Polynomial ℚ) (D : MvPolynomial σ ℚ),
      D.totalDegree ≤ b * d ∧
      (∀ a, (P a).natDegree ≤ d) ∧
      (∀ a (m : ℕ), (P a).eval (m : ℚ) = φ (FamilyNewton.Family.ordered T (fun i => e a i * m) x)) ∧
      (∀ a, (P a).coeff d = MvPolynomial.eval (fun j => (a j : ℚ)) D) := by
  let c := fun n => φ (FamilyNewton.Family.ordered (fun i => T i - 1) n x)
  have hc (n : Fin r → ℕ) (hn : d < ∑ i, n i) : c n = 0 := by
    rw [show c n = φ (FamilyNewton.Family.ordered (fun i => T i - 1) n x) from rfl, hzero n hn, map_zero]
  refine ⟨fun a => orbitPolynomial c d (fun i => (e a i : ℚ)), topPolynomial c d E,
    topPolynomial_totalDegree c d b E hE, fun a => orbitPolynomial_natDegree c d hc _, ?_, ?_⟩
  · intro a m
    rw [orbitPolynomial_eval]
    exact (FamilyNewton.Family.newton T φ x d hc (fun i => e a i * m)).symm
  · intro a
    have h := topPolynomial_eval c d hc E (fun j => (a j : ℚ))
    simpa only [he] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FamilyOrbitPolynomial.Family
