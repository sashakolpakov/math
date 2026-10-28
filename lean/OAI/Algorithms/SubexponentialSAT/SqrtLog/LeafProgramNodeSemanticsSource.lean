import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionDegree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentModel

namespace OAI.Algorithms

/-! Original IDs and fixed-high constants are retained in the source path.
All summation variables are free coordinates. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R V : Type*} [CommRing R] [Fintype V] [DecidableEq V]

/-- The row bank is indexed by factor and original variable ID. -/
def branchPath (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X])
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) : R[X] :=
  if hv : v ∈ H then Polynomial.C (HashInput.boolValue (high ⟨v,hv⟩))
  else ∑ w, rows i v w * Polynomial.C (HashInput.boolValue (x w))

theorem branchPath_origin (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X])
    (horigin : ∀ i (v : ResidualEmbedding.Free H) w,
      (rows i v.val w).eval 0 = if w=v then 1 else 0)
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) :
    (branchPath H high rows x i v).eval 0 =
      HashInput.boolValue (HighIncidence.glue H high x v) := by
  by_cases hv : v∈H
  · simp [branchPath,HighIncidence.glue,hv]
  · simp only [branchPath,dite_eq_right hv,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C]
    have hr := horigin i ⟨v,hv⟩
    simp only [hr,ite_mul,zero_mul,one_mul]
    simp [HighIncidence.glue,hv]

theorem branchPath_degree (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (r : ℕ)
    (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (x : ResidualEmbedding.Free H → Bool) (i : ℕ) (v : V) :
    (branchPath H high rows x i v).natDegree ≤ r := by
  unfold branchPath
  split
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro w _
    exact (Polynomial.natDegree_mul_C_le _ _).trans (hrows i v w)

/-- The bound is on the actual source target made from these rows. -/
theorem branch_target_degree (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (t k r : ℕ)
    (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (digits : Fin t → R[X]) (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (hwidth : ∀ ws ∈ hashes, ∀ w ∈ ws, w.2.length ≤ k) (hclause : clause.length ≤ k) :
    (target H t digits hashes marked clause (branchPath H high rows)).natDegree ≤
      Reconstruction.markedDegreeBound k r hashes.length t := by
  apply target_degree H t digits hdigits hashes marked clause _ k r
  · intro x i
    apply hashPath_degree hashes _ i k r
    · exact hwidth hashes[i] (List.getElem_mem i.isLt)
    · intro w hw l hl
      exact branchPath_degree H high rows r hrows x i.val l.variable
  · intro x
    unfold markedPath
    split
    · exact (clausePath_degree _ clause r (fun l _ =>
        branchPath_degree H high rows r hrows x hashes.length l.variable)).trans
        (Nat.mul_le_mul_right r hclause)
    · simp

/-- Neutral factors may enlarge the parameter count; they never enlarge the
source polynomial degree. -/
theorem branch_target_degree_lt (H : Finset V) (high : H → Bool)
    (rows : ℕ → V → ResidualEmbedding.Free H → R[X]) (t k r Q factors : ℕ)
    (hQ : 0 < Q) (hrows : ∀ i v w, (rows i v w).natDegree ≤ r)
    (digits : Fin t → R[X]) (hdigits : ∀ s, (digits s).natDegree ≤ 2)
    (hashes : List (SparseRow V R)) (marked : Bool) (clause : List (SAT.Literal V))
    (hwidth : ∀ ws ∈ hashes, ∀ w ∈ ws, w.2.length ≤ k) (hclause : clause.length ≤ k)
    (hcount : hashes.length ≤ factors) :
    (target H t digits hashes marked clause (branchPath H high rows)).natDegree <
      Q*Reconstruction.jetOrder (Reconstruction.markedDegreeBound k r factors t) Q := by
  apply (branch_target_degree H high rows t k r hrows digits hdigits hashes marked clause hwidth hclause).trans_lt
  apply lt_of_le_of_lt _ (Reconstruction.marked_degree_lt k r factors t Q hQ)
  unfold Reconstruction.markedDegreeBound
  gcongr

/-- Lift a sparse input row coefficient by coefficient, not by a nonexistent
ring homomorphism from the residue field into the thickened ring. -/
def liftedHashes {d : ℕ} (a : RingModel.Data d) (t : ℕ)
    (hashes : List (SparseRow V (ZMod 3))) : List (SparseRow V (a.O t)) :=
  hashes.map (fun ws => ws.map (fun w => (TernaryLift.coefficient a t w.1,w.2)))

omit [Fintype V] [DecidableEq V] in
theorem rowValue_map_coeff {C D S : Type*} [CommRing S]
    (lift : C → D) (decode : D → S) (value : V → S) (ws : SparseRow V C) :
    rowValue (ringAlgebra S) decode value (ws.map (fun w => (lift w.1,w.2))) =
      rowValue (ringAlgebra S) (decode ∘ lift) value ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons,rowValue,ih]; rfl

omit [Fintype V] [DecidableEq V] in
theorem liftedHashes_residue {d : ℕ} (a : RingModel.Data d) (t : ℕ) (ht : 0 < t)
    (hashes : List (SparseRow V (ZMod 3))) (x : V → Bool)
    (i : Fin (liftedHashes a t hashes).length) :
    a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=0 ∨
      a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=1 ∨
      a.rho t ht (sourceHash (liftedHashes a t hashes) x i)=2 := by
  apply Idempotent.model_residue_cases a
  have hi : (liftedHashes a t hashes)[i] ∈ liftedHashes a t hashes := List.getElem_mem i.isLt
  obtain ⟨ws,hws,he⟩ := List.mem_map.mp hi
  refine ⟨rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) ws,?_⟩
  change a.rho t ht (rowValue (ringAlgebra (a.O t)) id
    (fun v => HashInput.boolValue (x v)) (liftedHashes a t hashes)[i]) = _
  rw [← he,rowValue_map_coeff]
  exact TernaryLift.reduction_sparseRow a t ht x ws

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
