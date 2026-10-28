import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelIndexed

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodes_length_le (nodes : ℕ → List Bool) (Q N start count : ℕ)
    (hnodes : ∀ i < Q, (nodes i).length ≤ N) (hr : start+count ≤ Q) :
    (records (nodeSamples nodes) start count).flatten.length ≤ count*N := by
  induction count generalizing start with
  | zero => simp [records]
  | succ count ih =>
    have h := hnodes start (by omega)
    have ht := ih (start+1) (by omega)
    simp only [records,nodeSamples,List.flatten_cons,List.length_append]
    nlinarith

theorem loopBound_le (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet Q N K start count : ℕ)
    (hnodes : ∀ i < Q, (nodes i).length ≤ N) (hcost : ∀ i < Q, cost i ≤ K)
    (hr : start+count ≤ Q) :
    loopBound nodes cost maxJet start count ≤ count*(K+16*N+3*maxJet+22)+1 := by
  induction count generalizing start with
  | zero => simp [loopBound]
  | succ count ih =>
    have hn := hnodes start (by omega)
    have hc := hcost start (by omega)
    have ht := ih (start+1) (by omega)
    simp only [loopBound,callbackBound]
    nlinarith

/-- Every byte transfer and every worker invocation is included. -/
theorem collectBound_le (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet Q N K : ℕ) (oldNodes : List Bool)
    (hnodes : ∀ i < Q, (nodes i).length ≤ N) (hcost : ∀ i < Q, cost i ≤ K) :
    collectBound nodes cost maxJet oldNodes Q ≤
      Q*(K+33*N+6*maxJet+38)+2*oldNodes.length+26 := by
  have hn := nodes_length_le nodes Q N 0 Q hnodes (by omega)
  have hl := loopBound_le nodes cost maxJet Q N K 0 Q hnodes hcost (by omega)
  unfold collectBound
  rw [encoded_records_length]
  nlinarith

theorem collect_trace_uniform (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q N K : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (hnodes : ∀ i < Q, (nodes i).length ≤ N) (hcost : ∀ i < Q, cost i ≤ K)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ jets : Fin Q → List Bool, (∀ i, good Result maxJet i.val (jets i)) ∧
      ∃ time ≤ Q*(K+33*N+6*maxJet+38)+2*oldNodes.length+27, ∃ rr,
        RegFrame regs rr ∧ Trace (collectProgram worker) time
          ((state regs (initial frame oldNodes)).withPC (some (collectProgram worker).entry))
          ((state rr (finishedIndexed frame nodes jets)).withPC none) := by
  obtain ⟨jets,hjets,time,htime,rr,hf,he⟩ := collect_trace_indexed worker Valid nodes Result cost maxJet Q
    contract frame oldNodes regs hv hsource
  refine ⟨jets,hjets,time,?_,rr,hf,he⟩
  have hb := collectBound_le nodes cost maxJet Q N K oldNodes hnodes hcost
  omega

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
