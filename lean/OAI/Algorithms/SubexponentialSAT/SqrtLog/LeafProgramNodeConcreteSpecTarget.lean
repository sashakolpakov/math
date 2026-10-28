import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete

namespace OAI.Algorithms

/-! One source target is attached to the concrete factor specification. It
retains raw term multiplicity, optional marked violation, and shared U order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native

variable {r Q d n : ℕ}

def sourceHashes (q : Factor.Spec r Q n d) : List (SparseRow (Fin n) (ZMod 3)) :=
  q.rows.map (fun terms=>terms.map (fun term=>(term.2,HashInputProgram.Expansion.originalClause q.source term.1)))

def decodedHashes (q : Factor.Spec r Q n d) : List (SparseRow (Fin n) (q.p.model.O q.p.t)) :=
  (AssignmentConcrete.weightedHashes q).map (NativeSemantics.sourceTerms q.p.ops.decode)

theorem decodedHashes_lifted (q : Factor.Spec r Q n d) :
    decodedHashes q=NodeSemantics.liftedHashes q.p.model q.p.t (sourceHashes q) := by
  unfold decodedHashes AssignmentConcrete.weightedHashes NodeSemantics.liftedHashes sourceHashes
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro terms _
  have h := HashInputProgram.Expansion.weightedRow_decode q.p.t d q.p.ht q.p.hd
    q.p.model q.p.modulus q.p.cache q.source terms
  simpa only [NativeSemantics.sourceTerms,List.map_map,Function.comp_def,
    LayoutProgram.SourceBank.Parameters.ops] using h

@[simp] theorem sourceHashes_length (q : Factor.Spec r Q n d) :
    (sourceHashes q).length=q.rows.length := by simp [sourceHashes]

def specTarget (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool) :
    Polynomial (q.p.model.O q.p.t) :=
  NodeSemantics.target H q.p.t (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code)
    (decodedHashes q) q.marked q.markedClause
    (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H))

theorem specTarget_binary (q : Factor.Spec r Q n d)
    (M : SubexpPreparedQuartic.Modulus 3 q.p.t) (cache : RingProgram.ScalarCache 3 q.p.t)
    (half : RingProgram.ScalarCode 3 q.p.t)
    (hcode : q.code=IdempotentProgram.binaryLiftWords q.p.t M cache half)
    (H : Finset (Fin n)) (high : H → Bool) :
    specTarget q H high=binaryTarget q.p q.ps q.packing M cache half H high
      (sourceHashes q) q.marked q.markedClause := by
  unfold specTarget binaryTarget
  rw [hcode,decodedHashes_lifted,←binaryDigits_eq_code q.p M cache half q.ctx]

theorem specTarget_count (q : Factor.Spec r Q n d)
    (M : SubexpPreparedQuartic.Modulus 3 q.p.t) (cache : RingProgram.ScalarCache 3 q.p.t)
    (half : RingProgram.ScalarCode 3 q.p.t)
    (hcode : q.code=IdempotentProgram.binaryLiftWords q.p.t M cache half)
    (hhalf : 2*wordValue 3 q.p.t half=1)
    (H : Finset (Fin n)) (high : H → Bool) :
    (specTarget q H high).eval 0=
      (NodeSemantics.ternaryFixedHighCount H high (sourceHashes q) q.marked q.markedClause : q.p.model.O q.p.t) := by
  rw [specTarget_binary q M cache half hcode H high]
  exact binaryTarget_count q.p q.ps q.packing M cache half hhalf H high _ _ _

theorem sourceHashes_width (q : Factor.Spec r Q n d) (k : ℕ)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k) :
    ∀ ws∈sourceHashes q,∀ w∈ws,w.2.length ≤ k := by
  intro ws hws w hw
  obtain ⟨terms,ht,rfl⟩ := List.mem_map.mp hws
  obtain ⟨term,hterm,rfl⟩ := List.mem_map.mp hw
  apply hwidth
  exact List.getElem_mem _

theorem specTarget_degree (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool) (k factors : ℕ) (hQ : 0 < Q)
    (hwidth : ∀ clause∈q.source,clause.length ≤ k)
    (hfactors : q.rows.length ≤ factors) :
    (specTarget q H high).natDegree <
      Q*Reconstruction.jetOrder (Reconstruction.markedDegreeBound k q.p.R factors q.p.t) Q := by
  unfold specTarget
  rw [decodedHashes_lifted]
  apply NodeSemantics.branch_target_degree_lt H high (completedRows q.p q.ps q.packing H)
    q.p.t k q.p.R Q factors hQ (completedRows_degree q.p q.ps q.packing H) _
    (NodeSemantics.codeDigits_degree q.ctx (q.p.model.base q.p.t) q.code) _ q.marked q.markedClause
    (NodeSemantics.liftedHashes_width q.p.model q.p.t k _ (sourceHashes_width q k hwidth))
  · unfold Factor.Spec.markedClause
    by_cases h : q.mark < q.source.length
    · rw [List.getElem?_eq_getElem h,Option.getD_some]
      exact hwidth _ (List.getElem_mem h)
    · rw [List.getElem?_eq_none (by omega)]
      simp
  · simpa only [NodeSemantics.liftedHashes,List.length_map,sourceHashes_length] using hfactors

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
