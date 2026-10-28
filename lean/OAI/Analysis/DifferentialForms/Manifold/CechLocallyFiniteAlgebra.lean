import OAI.Analysis.DifferentialForms.Manifold.CechContractionAlgebra
import Mathlib.Algebra.BigOperators.Finprod

/-! # Cech Locally Finite Algebra -/

namespace OAI.Analysis.DifferentialForms.Manifold.CechLocallyFiniteAlgebra

noncomputable section

/-! The weighted Čech insertion identity for arbitrary index sets and finitely
supported weights. Local finiteness supplies this hypothesis pointwise. -/

open Function Set
open scoped BigOperators

variable {ι A : Type*} [AddCommGroup A] [Module ℂ A]

/-- Weighted insertion restricted to a specified finite set of indices. -/
def finsetWeightedInsertion {n : ℕ} (s : Finset ι) (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (a : Fin (n + 1) → ι) : A :=
  ∑ i ∈ s, weight i • c (Fin.cons i a)

theorem tupleCoboundary_finsetWeightedInsertion {n : ℕ} (s : Finset ι) (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (a : Fin (n + 2) → ι) :
    CechContractionAlgebra.tupleCoboundary (finsetWeightedInsertion s weight c) a +
      finsetWeightedInsertion s weight (CechContractionAlgebra.tupleCoboundary c) a =
        (∑ i ∈ s, weight i) • c a := by
  classical
  have hdouble :
      (∑ i ∈ s, weight i • ∑ j : Fin (n + 2),
        (-1 : ℤ) ^ j.val • c (Fin.cons i (a ∘ j.succAbove))) =
      CechContractionAlgebra.tupleCoboundary (finsetWeightedInsertion s weight c) a := by
    simp only [Finset.smul_sum, CechContractionAlgebra.tupleCoboundary, finsetWeightedInsertion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm (weight i) ((-1 : ℤ) ^ j.val) _
  have hidentity : finsetWeightedInsertion s weight (CechContractionAlgebra.tupleCoboundary c) a =
      (∑ i ∈ s, weight i) • c a - CechContractionAlgebra.tupleCoboundary (finsetWeightedInsertion s weight c) a := by
    unfold finsetWeightedInsertion
    simp_rw [CechContractionAlgebra.tupleCoboundary_cons, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    exact congrArg (fun z => (∑ i ∈ s, weight i) • c a - z) hdouble
  rw [hidentity]
  abel

/-- The actual pointwise `finsum` version of weighted insertion. -/
def finsumWeightedInsertion {n : ℕ} (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (a : Fin (n + 1) → ι) : A :=
  ∑ᶠ i, weight i • c (Fin.cons i a)

theorem finsumWeightedInsertion_eq_finset {n : ℕ} (s : Finset ι) (weight : ι → ℂ)
    (c : (Fin (n + 2) → ι) → A) (hs : support weight ⊆ s) :
    finsumWeightedInsertion weight c = finsetWeightedInsertion s weight c := by
  funext a
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hs
  intro hz
  apply hi
  change weight i • c (Fin.cons i a) = 0
  rw [hz]
  exact zero_smul ℂ _

/-- The Čech insertion identity needs only finitely many nonzero weights,
even when the index set and the tuple entries are arbitrary. -/
theorem tupleCoboundary_finsumWeightedInsertion {n : ℕ} (weight : ι → ℂ)
    (hweight : HasFiniteSupport weight) (c : (Fin (n + 2) → ι) → A)
    (a : Fin (n + 2) → ι) :
    CechContractionAlgebra.tupleCoboundary (finsumWeightedInsertion weight c) a +
      finsumWeightedInsertion weight (CechContractionAlgebra.tupleCoboundary c) a = (∑ᶠ i, weight i) • c a := by
  let s := hweight.toFinset
  have hs : support weight ⊆ s := by
    intro i hi
    exact hweight.mem_toFinset.mpr hi
  rw [finsumWeightedInsertion_eq_finset s weight c hs,
    finsumWeightedInsertion_eq_finset s weight (CechContractionAlgebra.tupleCoboundary c) hs,
    tupleCoboundary_finsetWeightedInsertion, finsum_eq_sum_of_support_subset weight hs]

end

end OAI.Analysis.DifferentialForms.Manifold.CechLocallyFiniteAlgebra
