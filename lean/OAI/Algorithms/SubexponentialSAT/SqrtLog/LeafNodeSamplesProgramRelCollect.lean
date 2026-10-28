import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelLoop

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem result_bounds {Result : ℕ → List Bool → Prop} {maxJet : ℕ}
    {indices : List ℕ} {jets : List (List Bool)}
    (h : List.Forall₂ (good Result maxJet) indices jets) :
    jets.length = indices.length ∧ jets.flatten.length ≤ indices.length*maxJet := by
  induction h with
  | nil => simp
  | @cons i jet indices jets hhead htail ih =>
    obtain ⟨hl,hb⟩ := ih
    have hj := hhead.2
    simp only [List.length_cons,List.flatten_cons,List.length_append]
    constructor
    · omega
    · nlinarith

def finished (frame : Fin 768 → List Bool) (nodes : ℕ → List Bool) (Q : ℕ)
    (jets : List (List Bool)) : Store :=
  {frame := frame, nodesOut := (records (nodeSamples nodes) 0 Q).flatten, jetsOut := jets.flatten}

def collectBound (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet : ℕ) (oldNodes : List Bool) (Q : ℕ) : ℕ :=
  7*(Encoding.encodeList id (records (nodeSamples nodes) 0 Q)).length +
    loopBound nodes cost maxJet 0 Q + 2*oldNodes.length +
    3*(records (nodeSamples nodes) 0 Q).flatten.length + 3*(Q*maxJet) + 2*Q + 18

theorem collect_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ jets, List.Forall₂ (good Result maxJet) (List.range' 0 Q) jets ∧
      ∃ time ≤ collectBound nodes cost maxJet oldNodes Q, ∃ rr,
        RegFrame regs rr ∧ Eval (collect worker) time (state regs (initial frame oldNodes))
          (state rr (finished frame nodes Q jets)) := by
  let s := initial frame oldNodes
  let a := {s with source := Encoding.encodeList id (records (nodeSamples nodes) 0 Q)}
  let r1 := readRegs regs 0 1 none
  have h300 : tapes s 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q) := by
    simpa [tapes,s,initial] using hsource
  have hc := copy_store regs s a 300 301 (by decide) (by decide) (by decide) rfl
    (by simp only [copyStacks,h300,tapes_source,update_source]; simp [a,s,initial])
  have hp := pop_ready r1 s (nodeSamples nodes) 0 Q
  obtain ⟨jets,hjets,time,htime,r2,hframe,hl⟩ := loop_eval worker Valid nodes Result cost maxJet Q contract
    0 Q (by omega) r1 s hv rfl rfl rfl rfl rfl
  obtain ⟨hjlen,hjbound⟩ := result_bounds hjets
  have hlen : jets.length = Q := by simpa using hjlen
  have hsize : jets.flatten.length ≤ Q*maxJet := by simpa using hjbound
  let b := finishLoop s nodes 0 jets
  have hb : b = {frame := frame, nodesRev := (records (nodeSamples nodes) 0 Q).flatten.reverse, jetsRev := jets.flatten.reverse, index := List.replicate Q true, nodesOut := oldNodes : Store} := by
    simp [b,finishLoop_eq,s,initial,hlen]
  let c := {b with nodesOut := []}
  let d := {c with nodesRev := [],nodesOut := (records (nodeSamples nodes) 0 Q).flatten}
  let e := {d with jetsRev := [],jetsOut := jets.flatten}
  let f := {e with index := []}
  let r3 := readRegs r2 0 1 none
  let r4 := readRegs r3 0 1 none
  let r5 := readRegs r4 0 1 none
  let r6 := readRegs r5 0 1 none
  have hclear := clear_store r2 b c 256 (by simp [c])
  have hnodes := transfer_store r3 c d 303 256 (by decide)
    (by simp [transferStacks,c,d,hb])
  have htransfer := transfer_store r4 d e 304 265 (by decide)
    (by simp [transferStacks,c,d,e,hb])
  have hindex := clear_store r5 e f 307 (by simp [f])
  refine ⟨jets,hjets,(7*(tapes s 300).length+5)+(1+(time+
    ((2*(tapes b 256).length+3)+((3*(tapes c 303).length+3)+
      ((3*(tapes d 304).length+3)+(2*(tapes e 307).length+3)))))),?_,r6,?_,?_⟩
  · simp only [collectBound,h300,tapes_nodesOut,tapes_nodesRev,tapes_jetsRev,tapes_index]
    simp only [c,d,e,hb,List.length_reverse,List.length_replicate]
    omega
  · exact (readRegs_frame regs).trans (hframe.trans ((readRegs_frame r2).trans
      ((readRegs_frame r3).trans ((readRegs_frame r4).trans (readRegs_frame r5)))))
  · have he := hc.seq (hp.seq (hl.seq (hclear.seq (hnodes.seq (htransfer.seq hindex)))))
    simpa only [collect,a,f,e,d,c,hb,s,initial,finished] using he

/-- Same finite collector program, with no reset or canonical-output premise. -/
theorem collect_trace (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (frame : Fin 768 → List Bool) (oldNodes : List Bool) (regs : Fin 40 → Bool)
    (hv : Valid frame)
    (hsource : frame 300 = Encoding.encodeList id (records (nodeSamples nodes) 0 Q)) :
    ∃ jets, List.Forall₂ (good Result maxJet) (List.range' 0 Q) jets ∧
      ∃ time ≤ collectBound nodes cost maxJet oldNodes Q+1, ∃ rr,
        RegFrame regs rr ∧
        Trace (collectProgram worker) time
          ((state regs (initial frame oldNodes)).withPC (some (collectProgram worker).entry))
          ((state rr (finished frame nodes Q jets)).withPC none) := by
  obtain ⟨jets,hjets,time,htime,rr,hf,he⟩ := collect_eval worker Valid nodes Result cost maxJet Q contract
    frame oldNodes regs hv hsource
  exact ⟨jets,hjets,time+1,Nat.add_le_add_right htime 1,rr,hf,compiled_halt_trace he 300 265⟩

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
