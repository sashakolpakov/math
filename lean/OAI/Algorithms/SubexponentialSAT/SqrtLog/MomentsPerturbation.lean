import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSquarefree

namespace OAI.Algorithms

/-! Actual row perturbations, rather than an assumed support invariant.
Every formal Boolean coordinate is multiplied by a polynomial with zero
constant term in Z. The construction is valid over any commutative ring. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable def rowDelta (p : Polynomial R) (theta : R) : Polynomial R :=
  p.comp (Polynomial.X + Polynomial.C theta) - Polynomial.C (p.eval theta)

@[simp] theorem rowDelta_coeff_zero (p : Polynomial R) (theta : R) :
    (rowDelta p theta).coeff 0 = 0 := by
  simp [rowDelta, Polynomial.coeff_zero_eq_eval_zero]

noncomputable def variableZ (v : V) (p : Polynomial R) : ZJet V R :=
  p.map Squarefree.scalar * Polynomial.C (Squarefree.monomial {v} 1)

theorem variableZ_coeff (v : V) (p : Polynomial R) (j : ℕ) :
    (variableZ v p).coeff j = Squarefree.monomial {v} (p.coeff j) := by
  simp only [variableZ, Polynomial.coeff_mul_C, Polynomial.coeff_map]
  change Squarefree.monomial ∅ (p.coeff j) * Squarefree.monomial {v} 1 = _
  simp

theorem variableZ_admissible (v : V) (p : Polynomial R) (hp : p.coeff 0 = 0) :
    ZAdmissible (variableZ v p) := by
  intro j
  rw [variableZ_coeff]
  by_cases hj : j = 0
  · subst j
    simp only [hp]
    simpa [Squarefree.monomial] using (bounded_zero (V := V) (R := R) 0)
  · apply bounded_monomial
    simp only [Finset.card_singleton]
    omega

noncomputable def incidenceZ [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    ZJet V R :=
  Polynomial.C (Squarefree.scalar beta) + ∑ v, variableZ v (rowDelta (row v) theta)

theorem incidenceZ_admissible [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    ZAdmissible (incidenceZ row theta beta) := by
  apply ZAdmissible.add
  · apply zAdmissible_monomial 0
    exact bounded_monomial ∅ beta (by simp)
  · apply zAdmissible_sum
    intro v hv
    exact variableZ_admissible v _ (rowDelta_coeff_zero (row v) theta)

noncomputable def incidenceJet [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    Jet V R := Polynomial.C (incidenceZ row theta beta)

theorem incidenceJet_admissible [Fintype V] (row : V → Polynomial R) (theta beta : R) :
    Admissible (incidenceJet row theta beta) :=
  admissible_monomial 0 _ (incidenceZ_admissible row theta beta)

@[simp] theorem eval_scalar (x : V → R) (hx : ∀ v, x v * x v = x v) (c : R) :
    Squarefree.evalHom x hx (Squarefree.scalar c) = c := by
  change Squarefree.evalHom x hx (Squarefree.monomial ∅ c) = c
  simp [Squarefree.weight]

theorem variableZ_eval (x : V → R) (hx : ∀ v, x v * x v = x v)
    (v : V) (p : Polynomial R) :
    (variableZ v p).map (Squarefree.evalHom x hx) = p * Polynomial.C (x v) := by
  ext j
  simp [variableZ_coeff, Polynomial.coeff_mul_C, Squarefree.weight]

theorem incidenceZ_eval [Fintype V] (x : V → R) (hx : ∀ v, x v * x v = x v)
    (row : V → Polynomial R) (theta beta : R) :
    (incidenceZ row theta beta).map (Squarefree.evalHom x hx) =
      Polynomial.C beta + ∑ v, rowDelta (row v) theta * Polynomial.C (x v) := by
  simp only [incidenceZ, Polynomial.map_add, Polynomial.map_C, eval_scalar, Polynomial.map_sum]
  simp_rw [variableZ_eval]


/-- Restoring the node value gives exactly the common shifted incidence row. -/
theorem incidenceZ_eval_row [Fintype V] (x : V → R) (hx : ∀ v, x v * x v = x v)
    (row : V → Polynomial R) (theta beta : R)
    (hbeta : beta = ∑ v, (row v).eval theta * x v) :
    (incidenceZ row theta beta).map (Squarefree.evalHom x hx) =
      ∑ v, (row v).comp (Polynomial.X + Polynomial.C theta) * Polynomial.C (x v) := by
  rw [incidenceZ_eval, hbeta, map_sum]
  simp only [rowDelta, sub_mul, ← Polynomial.C_mul]
  rw [Finset.sum_sub_distrib]
  ring

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
