import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel

/-! # Cech Contraction Algebra -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechContractionAlgebra

/-!
The finite-sum identity behind the usual partition-of-unity Čech contraction.
It is proved for arbitrary module-valued tuple families, then used for the
actual restricted sections in `ManifoldCechContraction`.
-/

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [AddCommGroup A] [Module ℂ A]

/-- Alternating deletion on a tuple-indexed module-valued family. -/
def tupleCoboundary {n : ℕ} (c : (Fin (n + 1) → ι) → A)
    (a : Fin (n + 2) → ι) : A :=
  ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • c (a ∘ j.succAbove)

/-- Insert an initial index and sum with the indicated scalar weights. -/
def weightedInsertion {n : ℕ} (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (a : Fin (n + 1) → ι) : A :=
  ∑ i, weight i • c (Fin.cons i a)

omit [Fintype ι] [Module ℂ A] in
/-- The first deletion removes the inserted index; all other deletions shift
the sign once. -/
theorem tupleCoboundary_cons {n : ℕ} (c : (Fin (n + 2) → ι) → A)
    (i : ι) (a : Fin (n + 2) → ι) :
    tupleCoboundary c (Fin.cons i a) =
      c a - ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • c (Fin.cons i (a ∘ j.succAbove)) := by
  classical
  rw [tupleCoboundary, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Fin.cons_comp_succ_succAbove, Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

/-- The explicit finite-sum contraction identity, before evaluating the sum
of the weights. -/
theorem tupleCoboundary_weightedInsertion {n : ℕ} (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (a : Fin (n + 2) → ι) :
    tupleCoboundary (weightedInsertion weight c) a +
      weightedInsertion weight (tupleCoboundary c) a = (∑ i, weight i) • c a := by
  classical
  have hdouble :
      (∑ i, weight i • ∑ j : Fin (n + 2),
        (-1 : ℤ) ^ j.val • c (Fin.cons i (a ∘ j.succAbove))) =
      tupleCoboundary (weightedInsertion weight c) a := by
    simp only [Finset.smul_sum, tupleCoboundary, weightedInsertion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm (weight i) ((-1 : ℤ) ^ j.val) _
  have hidentity : weightedInsertion weight (tupleCoboundary c) a =
      (∑ i, weight i) • c a - tupleCoboundary (weightedInsertion weight c) a := by
    unfold weightedInsertion
    simp_rw [tupleCoboundary_cons, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    exact congrArg (fun z => (∑ i, weight i) • c a - z) hdouble
  rw [hidentity]
  abel

end OAI.Analysis.DifferentialForms.Manifold.CechContractionAlgebra
