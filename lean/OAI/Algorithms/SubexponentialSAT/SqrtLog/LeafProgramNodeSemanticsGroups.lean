import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsFactors

namespace OAI.Algorithms

/-! Exact assembly of all colored factor lists, including optional marking
and neutral IDs. Neither list order nor neutral padding changes the target. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {A : Type*} [CommMonoid A]

theorem prod_colored_lists {G : Type*} [Fintype G] [DecidableEq G]
    (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → G) (f : ℕ → A) :
    (∏ g, ((ids.filter (fun i => color i = g)).map f).prod) = (ids.map f).prod := by
  rw [← List.prod_toFinset f hn]
  have he (g : G) : ((ids.filter (fun i => color i=g)).map f).prod =
      ∏ i ∈ ids.toFinset.filter (fun i => color i=g), f i := by
    rw [← List.prod_toFinset f (hn.filter _)]
    congr 1
    ext i
    simp
  simp_rw [he]
  exact Finset.prod_fiberwise ids.toFinset color f

theorem prod_ids_split (q : ℕ) (marked : Bool) (ids : List ℕ) (hn : ids.Nodup)
    (hhash : ∀ i < q, i∈ids) (hmark : marked=true → q∈ids) (f : ℕ → A)
    (hother : ∀ i, i ∈ ids → q ≤ i → (¬ (marked = true ∧ i = q)) → f i = 1) :
    (ids.map f).prod = (∏ i : Fin q, f i.val) * (if marked then f q else 1) := by
  rw [← List.prod_toFinset f hn,Fin.prod_univ_eq_prod_range]
  cases hm : marked
  · simp only [Bool.false_eq_true,ite_false,mul_one]
    symm
    apply Finset.prod_subset
    · intro i hi
      exact List.mem_toFinset.mpr (hhash i (Finset.mem_range.mp hi))
    · intro i hi hnq
      exact hother i (List.mem_toFinset.mp hi) (by simpa using hnq) (by simp [hm])
  · simp only [ite_true]
    rw [← Finset.prod_range_succ]
    symm
    apply Finset.prod_subset
    · intro i hi
      have hh := Finset.mem_range.mp hi
      exact List.mem_toFinset.mpr (if h : i < q then hhash i h else by
        have he : i=q := by omega
        rw [he]
        exact hmark hm)
    · intro i hi hnq
      have hh : q < i := by simpa using hnq
      exact hother i (List.mem_toFinset.mp hi) (by omega) (by omega)

variable {R : Type*} [CommRing R] {n : ℕ}

def selectedExpression (u : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X]) (id : ℕ) :
    Polynomial R[X] :=
  if h : id < hashes.length then
    TotalOrder.row u (digitAt digits (hashPath hashes path ⟨id,h⟩))
      (IdempotentProgram.hValue (hashPath hashes path ⟨id,h⟩))
  else if marked && decide (id=hashes.length) then
    Polynomial.C (clauseValue (ringAlgebra R[X]) (path id) clause)
  else 1

theorem selectedExpression_product (u : ℕ) (digits : Fin u → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X])
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i∈ids)
    (hm : marked=true → hashes.length∈ids) :
    (ids.map (selectedExpression u digits hashes marked clause path)).prod =
      queryExpansion u digits hashes marked clause path := by
  rw [prod_ids_split hashes.length marked ids hn hh hm]
  · unfold queryExpansion TotalOrder.fullProduct
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      simp only [selectedExpression,dite_eq_left i.isLt]
    · cases hb : marked <;> simp [selectedExpression,markedPath]
  · intro i hi hq hm'
    simp only [selectedExpression,dite_eq_right (by omega : ¬i < hashes.length)]
    have he : ¬(marked && decide (i=hashes.length))=true := by simpa using hm'
    simp only [ite_eq_right he]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
