import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelCollect

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev indexedJets {Q : ℕ} (jets : List (List Bool)) (h : jets.length = Q)
    (i : Fin Q) : List Bool := jets.get ⟨i.val,by omega⟩

theorem indexedJets_map {Q : ℕ} (jets : List (List Bool)) (h : jets.length = Q) :
    (List.finRange Q).map (indexedJets jets h) = jets := by
  subst Q
  simpa only [indexedJets] using List.finRange_map_get jets

theorem indexedJets_good {Result : ℕ → List Bool → Prop} {maxJet Q : ℕ}
    {jets : List (List Bool)}
    (h : List.Forall₂ (good Result maxJet) (List.range' 0 Q) jets)
    (hlen : jets.length = Q) (i : Fin Q) :
    good Result maxJet i.val (indexedJets jets hlen i) := by
  have hi : i.val < (List.range' 0 Q).length := by simp
  have hj : i.val < jets.length := by omega
  have hg := h.get hi hj
  simpa [indexedJets,List.get_eq_getElem,List.getElem_range'_1] using hg

abbrev finishedIndexed (frame : Fin 768 → List Bool) (nodes : ℕ → List Bool)
    {Q : ℕ} (jets : Fin Q → List Bool) : Store :=
  {frame := frame, nodesOut := ((List.finRange Q).map (fun i => nodes i.val)).flatten,
    jetsOut := ((List.finRange Q).map jets).flatten}

theorem finished_indexed {Q : ℕ} (frame : Fin 768 → List Bool) (nodes : ℕ → List Bool)
    (jets : List (List Bool)) (h : jets.length = Q) :
    finishedIndexed frame nodes (indexedJets jets h) = finished frame nodes Q jets := by
  simp only [finishedIndexed,finished,indexedJets_map,records_eq_finRange,nodeSamples]

theorem collect_eval_indexed (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ jets : Fin Q → List Bool, (∀ i, good Result maxJet i.val (jets i)) ∧
      ∃ time ≤ collectBound nodes cost maxJet oldNodes Q, ∃ rr,
        RegFrame regs rr ∧ Eval (collect worker) time (state regs (initial frame oldNodes))
          (state rr (finishedIndexed frame nodes jets)) := by
  obtain ⟨jets,hjets,time,htime,rr,hf,he⟩ := collect_eval worker Valid nodes Result cost maxJet Q contract
    frame oldNodes regs hv hsource
  have hlen : jets.length = Q := by simpa using (result_bounds hjets).1
  refine ⟨indexedJets jets hlen,indexedJets_good hjets hlen,time,htime,rr,hf,?_⟩
  simpa only [finished_indexed] using he

theorem collect_trace_indexed (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ jets : Fin Q → List Bool, (∀ i, good Result maxJet i.val (jets i)) ∧
      ∃ time ≤ collectBound nodes cost maxJet oldNodes Q+1, ∃ rr,
        RegFrame regs rr ∧ Trace (collectProgram worker) time
          ((state regs (initial frame oldNodes)).withPC (some (collectProgram worker).entry))
          ((state rr (finishedIndexed frame nodes jets)).withPC none) := by
  obtain ⟨jets,hjets,time,htime,rr,hf,he⟩ := collect_eval_indexed worker Valid nodes Result cost maxJet Q contract
    frame oldNodes regs hv hsource
  exact ⟨jets,hjets,time+1,Nat.add_le_add_right htime 1,rr,hf,compiled_halt_trace he 300 265⟩

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
