import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
universe u

/-- Witness data belong to the proof of an actual returned byte string.
They need not be uniquely determined by its denotation or by the node. -/
def WitnessResult (Entry : ℕ → Type u) (encode : (i : ℕ) → Entry i → List Bool)
    (ValidEntry : (i : ℕ) → Entry i → Prop) (i : ℕ) (jet : List Bool) : Prop :=
  ∃ entry, ValidEntry i entry ∧ jet = encode i entry

theorem collect_eval_witness (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Entry : ℕ → Type u)
    (encode : (i : ℕ) → Entry i → List Bool) (ValidEntry : (i : ℕ) → Entry i → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes (WitnessResult Entry encode ValidEntry) cost maxJet Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ entries : (i : Fin Q) → Entry i.val,
      (∀ i, ValidEntry i.val (entries i) ∧ (encode i.val (entries i)).length ≤ maxJet) ∧
      ∃ time ≤ collectBound nodes cost maxJet oldNodes Q, ∃ rr,
        RegFrame regs rr ∧ Eval (collect worker) time (state regs (initial frame oldNodes))
          (state rr (finishedIndexed frame nodes (fun i => encode i.val (entries i)))) := by
  classical
  obtain ⟨jets,hjets,time,htime,rr,hf,he⟩ := collect_eval_indexed worker Valid nodes
    (WitnessResult Entry encode ValidEntry) cost maxJet Q contract frame oldNodes regs hv hsource
  have hw : ∀ i : Fin Q, ∃ entry : Entry i.val,
      ValidEntry i.val entry ∧ jets i = encode i.val entry := fun i => (hjets i).1
  choose entries hvalid hencode using hw
  have hj : jets = fun i => encode i.val (entries i) := funext hencode
  refine ⟨entries,?_,time,htime,rr,hf,?_⟩
  · intro i
    exact ⟨hvalid i,by simpa only [hencode i] using (hjets i).2⟩
  · simpa only [hj] using he

theorem collect_trace_witness (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Entry : ℕ → Type u)
    (encode : (i : ℕ) → Entry i → List Bool) (ValidEntry : (i : ℕ) → Entry i → Prop)
    (cost : ℕ → ℕ) (maxJet Q N K : ℕ)
    (contract : WorkerContract worker Valid nodes (WitnessResult Entry encode ValidEntry) cost maxJet Q)
    (hnodes : ∀ i < Q, (nodes i).length ≤ N) (hcost : ∀ i < Q, cost i ≤ K)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ entries : (i : Fin Q) → Entry i.val,
      (∀ i, ValidEntry i.val (entries i) ∧ (encode i.val (entries i)).length ≤ maxJet) ∧
      ∃ time ≤ Q*(K+33*N+6*maxJet+38)+2*oldNodes.length+27, ∃ rr,
        RegFrame regs rr ∧ Trace (collectProgram worker) time
          ((state regs (initial frame oldNodes)).withPC (some (collectProgram worker).entry))
          ((state rr (finishedIndexed frame nodes (fun i => encode i.val (entries i)))).withPC none) := by
  obtain ⟨entries,hentries,time,htime,rr,hf,he⟩ := collect_eval_witness worker Valid nodes Entry encode
    ValidEntry cost maxJet Q contract frame oldNodes regs hv hsource
  refine ⟨entries,hentries,time+1,?_,rr,hf,compiled_halt_trace he 300 265⟩
  have hb := collectBound_le nodes cost maxJet Q N K oldNodes hnodes hcost
  omega

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
