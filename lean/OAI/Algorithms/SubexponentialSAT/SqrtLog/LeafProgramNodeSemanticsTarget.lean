import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderPathDegree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderIndicator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLift

namespace OAI.Algorithms

/-! The reconstruction target retains one shared total U-order. Its source
rows retain original variable identifiers, and its outer sum is over free
Boolean assignments in one fixed-high branch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [Fintype V] [DecidableEq V]

/-- A row is evaluated as the supplied sparse clause circuit. -/
abbrev hashPath (hashes : List (SparseRow V R))
    (path : ℕ → V → R[X]) (i : Fin hashes.length) : R[X] :=
  rowValue (ringAlgebra R[X]) Polynomial.C (path i.val) hashes[i]

def markedPath (hashes : List (SparseRow V R)) (marked : Bool)
    (clause : List (SAT.Literal V)) (path : ℕ → V → R[X]) : R[X] :=
  if marked then clauseValue (ringAlgebra R[X]) (path hashes.length) clause else 1

/-- The digit family may be the actual computed coefficient array; there is
no assumption that its untruncated product has the required small degree. -/
def digitAt {t : ℕ} (digits : Fin t → R[X]) (L : R[X]) (j : ℕ) : R[X] :=
  if hj : j < t then (digits ⟨j,hj⟩).comp L else 0

def queryPolynomial (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) : R[X] :=
  TotalOrder.output Finset.univ t
    (fun i => digitAt digits (hashPath hashes path i))
    (fun i => IdempotentProgram.hValue (hashPath hashes path i)) *
      markedPath hashes marked clause path

def target (H : Finset V) (t : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X]) : R[X] :=
  ∑ x, queryPolynomial t digits hashes marked clause (path x)

omit [Fintype V] [DecidableEq V] in
theorem literalPath_degree (path : V → R[X]) (l : SAT.Literal V) (r : ℕ)
    (h : (path l.variable).natDegree ≤ r) :
    (literalValue (ringAlgebra R[X]) path l).natDegree ≤ r := by
  cases hp : l.positive
  · simpa [literalValue,ringAlgebra,hp] using h
  · simp only [literalValue,hp,ite_true,ringAlgebra]
    change (1 + -(path l.variable)).natDegree ≤ r
    exact (Polynomial.natDegree_add_le _ _).trans (by simpa using h)

omit [Fintype V] [DecidableEq V] in
theorem clausePath_degree (path : V → R[X]) (ls : List (SAT.Literal V)) (r : ℕ)
    (h : ∀ l ∈ ls, (path l.variable).natDegree ≤ r) :
    (clauseValue (ringAlgebra R[X]) path ls).natDegree ≤ ls.length*r := by
  induction ls with
  | nil => simp [clauseValue,ringAlgebra]
  | cons l ls ih =>
    change (literalValue (ringAlgebra R[X]) path l *
      clauseValue (ringAlgebra R[X]) path ls).natDegree ≤ (l::ls).length*r
    apply Polynomial.natDegree_mul_le.trans
    have h1 := literalPath_degree path l r (h l (by simp))
    have h2 := ih (fun a ha => h a (by simp [ha]))
    simpa [Nat.add_mul,Nat.add_comm] using Nat.add_le_add h1 h2

omit [Fintype V] [DecidableEq V] in
theorem hashPath_degree (hashes : List (SparseRow V R)) (path : ℕ → V → R[X])
    (i : Fin hashes.length) (k r : ℕ)
    (hwidth : ∀ w ∈ hashes[i], w.2.length ≤ k)
    (hpath : ∀ w ∈ hashes[i], ∀ l ∈ w.2, (path i.val l.variable).natDegree ≤ r) :
    (hashPath hashes path i).natDegree ≤ k*r := by
  unfold hashPath
  generalize hashes[i] = ws at *
  induction ws with
  | nil => simp [rowValue,ringAlgebra]
  | cons w ws ih =>
    change (Polynomial.C w.1 * clauseValue (ringAlgebra R[X]) (path i.val) w.2 +
      rowValue (ringAlgebra R[X]) Polynomial.C (path i.val) ws).natDegree ≤ k*r
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      exact (clausePath_degree _ _ r (hpath w (by simp))).trans
        (Nat.mul_le_mul_right r (hwidth w (by simp)))
    · exact ih (fun a ha => hwidth a (by simp [ha]))
        (fun a ha => hpath a (by simp [ha]))

theorem hValue_degree (L : R[X]) (k : ℕ) (hL : L.natDegree ≤ k) :
    (IdempotentProgram.hValue L).natDegree ≤ k*3 := by
  have hs (c : R) : (L - Polynomial.C c).natDegree ≤ k :=
    (Polynomial.natDegree_sub_le _ _).trans (by simpa using hL)
  have h := Nat.add_le_add (Nat.add_le_add hL (hs 1)) (hs 2)
  have hp : (IdempotentProgram.hValue L).natDegree ≤
      L.natDegree + (L-1).natDegree + (L-2).natDegree :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add_right Polynomial.natDegree_mul_le _)
  change L.natDegree + (L-1).natDegree + (L-2).natDegree ≤ k+k+k at h
  exact hp.trans (h.trans_eq (by omega))

omit [Fintype V] [DecidableEq V] in
theorem queryPolynomial_degree (t : ℕ) (digits : Fin t → R[X])
    (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : ℕ → V → R[X]) (k r : ℕ)
    (hhash : ∀ i, (hashPath hashes path i).natDegree ≤ k*r)
    (hmark : (markedPath hashes marked clause path).natDegree ≤ k*r) :
    (queryPolynomial t digits hashes marked clause path).natDegree ≤
      k*r*(2*hashes.length+3*(t-1)+1) := by
  have he : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)), ∀ j < t,
      (digitAt digits (hashPath hashes path i) j).natDegree ≤ (k*r)*(3-1) := by
    intro i _ j hj
    simp only [digitAt,dite_eq_left hj]
    exact Polynomial.natDegree_comp_le.trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul (hdigits ⟨j,hj⟩) (hhash i))
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin hashes.length)),
      (IdempotentProgram.hValue (hashPath hashes path i)).natDegree ≤ (k*r)*3 :=
    fun i _ => hValue_degree _ _ (hhash i)
  have ho := TotalOrder.output_pathDegree_hash_bound Finset.univ t 3 (k*r) _ _ he hh
  have hb := Polynomial.natDegree_mul_le.trans (Nat.add_le_add ho hmark)
  simpa [queryPolynomial,Finset.card_univ, Nat.mul_add, Nat.mul_comm,Nat.mul_left_comm] using hb

theorem target_degree (H : Finset V) (t : ℕ) (digits : Fin t → R[X])
    (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (path : (ResidualEmbedding.Free H → Bool) → ℕ → V → R[X]) (k r : ℕ)
    (hhash : ∀ x i, (hashPath hashes (path x) i).natDegree ≤ k*r)
    (hmark : ∀ x, (markedPath hashes marked clause (path x)).natDegree ≤ k*r) :
    (target H t digits hashes marked clause path).natDegree ≤
      k*r*(2*hashes.length+3*(t-1)+1) := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  exact queryPolynomial_degree t digits hdigits hashes marked clause (path x) k r (hhash x) (hmark x)

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
