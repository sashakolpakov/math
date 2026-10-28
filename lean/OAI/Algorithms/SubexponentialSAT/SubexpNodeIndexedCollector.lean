import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideOrder

namespace OAI.Algorithms

/-! Indexed outputs of the installed worker feed the actual ordered
collector. The rank is fixed by the physically generated node table; no
permutation premise is introduced by this final control-flow adapter. -/

namespace SubexponentialSAT.SubexpNodeIndexedCollector

open BitProgram StructuredCalls SubexpNodeWorkspace
open SubexpNodeWideLoop

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p 1)

/-- A proof-level reading of the table's actual rank. The machine computes
this rank using NodeIndexProgram before invoking the per-node producers. -/
def indexed (jet : Fin (p^4-1) → List Bool) (bits : List Bool) : List Bool :=
  let i := (SubexpNodeLiftData.liftedNodeWords p (D+1) M).idxOf bits
  if h : i < p^4-1 then jet ⟨i,h⟩ else []

theorem indexed_word (jet : Fin (p^4-1) → List Bool) (i : Fin (p^4-1)) :
    indexed p D M jet (SubexpNodeIndexSemantics.thetaWord p D i) = jet i := by
  simp only [indexed,SubexpNodeIndexSemantics.idxOf_thetaWord]
  rw [dite_eq_left i.isLt]

variable (masters : SubexpNodeWorkspace.Store) (shape : List Bool)
  (jet : Fin (p^4-1) → List Bool) (bound : ℕ)

/-- The premise is the concrete worker's indexed execution theorem. This
adapter supplies only activation, restored workspace and protected frames. -/
theorem contract
    (run : ∀ (i : Fin (p^4-1)) (d : State 16 288),
      d.stacks = activeStacks masters (SubexpNodeIndexSemantics.thetaWord p D i) →
      ∃ n ≤ bound, ∃ out : State 16 288,
        Trace SubexpNodeConcretePipeline.worker n
          (d.withPC (some SubexpNodeConcretePipeline.worker.entry)) (out.withPC none) ∧
        out.stacks = finalStacks masters (jet i) shape) :
    NodeContract SubexpNodeConcretePipeline.worker
      (fun bits => bits ∈ SubexpNodeLiftData.liftedNodeWords p (D+1) M)
      (SubexpNodeWorkspace.Ready masters) shape (indexed p D M jet) (fun _ => bound) := by
  intro bits d hb hw htheta _ _
  obtain ⟨i,hi⟩ := (SubexpNodeIndexSemantics.mem_liftedNodeWords_iff p (D+1) M
    (Nat.succ_pos D) bits).mp hb
  have hactive : d.stacks = activeStacks masters (SubexpNodeIndexSemantics.thetaWord p D i) := by
    have ha := active_from_ready bits hw htheta
    simpa only [SubexpNodeIndexSemantics.thetaWord,hi] using ha
  obtain ⟨n,hn,out,ht,hs⟩ := run i d hactive
  refine ⟨n,hn,out,ht,?_,?_,?_,?_,?_⟩
  · rw [hs]
    rfl
  · rw [hs]
    change jet i = indexed p D M jet bits
    rw [← hi]
    exact (indexed_word p D M jet i).symm
  · rw [hs]
    exact Function.update_self _ _ _
  · rw [hs]
    exact final_ready masters (jet i) shape
  · intro j hj
    rw [hs,hactive]
    exact final_protected masters _ (jet i) shape j hj

/-- The actual generated table is consumed in its own order and the actual
flat jets are emitted in that same order, ready for the CRT input arrays. -/
theorem program_runs
    (run : ∀ (i : Fin (p^4-1)) (d : State 16 288),
      d.stacks = activeStacks masters (SubexpNodeIndexSemantics.thetaWord p D i) →
      ∃ n ≤ bound, ∃ out : State 16 288,
        Trace SubexpNodeConcretePipeline.worker n
          (d.withPC (some SubexpNodeConcretePipeline.worker.entry)) (out.withPC none) ∧
        out.stacks = finalStacks masters (jet i) shape)
    (d : State 16 352) (hr : Ready (SubexpNodeWorkspace.Ready masters) d)
    (hm : d.stacks 332 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D+1) M))
    (h333 : d.stacks 333 = []) (h334 : d.stacks 334 = [])
    (h335 : d.stacks 335 = []) (h336 : d.stacks 336 = [])
    (h288 : d.stacks 288 = []) (h297 : d.stacks 297 = []) :
    ∃ out : State 16 352,
      RunsIn SubexpNodeConcretePipeline.program
        (totalCost (fun _ => bound) shape (indexed p D M jet)
          (SubexpNodeLiftData.liftedNodeWords p (D+1) M) + 1)
        (d.withPC (some SubexpNodeConcretePipeline.program.entry)) (out.withPC none) ∧
      Ready (SubexpNodeWorkspace.Ready masters) out ∧
      out.stacks 288 = (List.ofFn (SubexpNodeIndexSemantics.thetaWord p D)).flatten ∧
      out.stacks 297 = (List.ofFn jet).flatten ∧
      out.stacks 332 = d.stacks 332 ∧
      out.stacks 333 = [] ∧ out.stacks 334 = [] ∧ out.stacks 335 = [] ∧ out.stacks 336 = [] ∧
      (∀ i : Fin 288, ProtectedBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) := by
  obtain ⟨out,he,ho,hn,hj,rest⟩ := SubexpNodeWideOrder.program_runs p (D+1) M
    SubexpNodeConcretePipeline.worker (SubexpNodeWorkspace.Ready masters) shape
    (indexed p D M jet) (fun _ => bound) (contract p D M masters shape jet bound run)
    (Nat.succ_pos D) d hr hm h333 h334 h335 h336 h288 h297
  refine ⟨out,he,ho,hn,?_,rest⟩
  rw [hj]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact indexed_word p D M jet i

end SubexponentialSAT.SubexpNodeIndexedCollector

end OAI.Algorithms
