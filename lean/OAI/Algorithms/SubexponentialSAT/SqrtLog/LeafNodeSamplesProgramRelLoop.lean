import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgramRelCore

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem loop_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q)
    (start count : ℕ) (hrange : start+count ≤ Q) (regs : Fin 40 → Bool)
    (s : Store) (hv : Valid s.frame) (hx : s.index = List.replicate start true)
    (hn : s.node = []) (hj : s.jet = []) (hs : s.shape = []) (ht : s.temporary = []) :
    ∃ jets, List.Forall₂ (good Result maxJet) (List.range' start count) jets ∧
      ∃ time ≤ loopBound nodes cost maxJet start count, ∃ rr,
        RegFrame regs rr ∧
        Eval (loop worker) time (ready regs s (nodeSamples nodes) start count)
          (state rr (finishLoop s nodes start jets)) := by
  induction count generalizing start regs s with
  | zero =>
    refine ⟨[],List.Forall₂.nil,1,le_rfl,parserRegs regs false true (regs 39),
      parserRegs_frame _ _ _ _,?_⟩
    apply Eval.while_false
    simp [ready,state,parserRegs]
  | succ count ih =>
    let tail := Encoding.encodeList id (records (nodeSamples nodes) (start+1) count)
    let a := {s with source := Encoding.frame (nodes start) ++ tail,payload := []}
    let b := {s with source := tail,payload := (nodes start).reverse}
    let r0 := parserRegs regs true true (regs 39)
    let r1 := parserRegs r0 false true (r0 39)
    have hread : Eval reader (6*(nodes start).length+4)
        (ready regs s (nodeSamples nodes) start (count+1)) (state r1 b) := by
      simpa [ready,nodeSamples,a,b,tail,r0,r1] using reader_store r0 a (nodes start) tail rfl rfl
    obtain ⟨jet,hjet,c,hc,r2,hcf,hcall⟩ := callback_eval worker Valid nodes Result cost maxJet Q start
      contract (by omega) r1 b hv (by simpa [b] using hx) rfl
      (by simpa [b] using hn) (by simpa [b] using hj)
      (by simpa [b] using hs) (by simpa [b] using ht)
    have hcall' : Eval (callback worker) c (state r1 b)
        (state r2 {advanceResult s nodes start jet with source := tail,payload := []}) := by
      simpa [b,advanceResult,advance] using hcall
    have hpop := pop_ready r2 (advanceResult s nodes start jet) (nodeSamples nodes) (start+1) count
    have hx' : (advanceResult s nodes start jet).index = List.replicate (start+1) true := by
      simp [advanceResult,advance,hx,List.replicate_succ]
    obtain ⟨jets,hjets,u,hu,r3,hrf,hrest⟩ := ih (start+1) (by omega) r2
      (advanceResult s nodes start jet) hv hx'
      (by simpa [advanceResult] using hn) (by simpa [advanceResult] using hj)
      (by simpa [advanceResult] using hs) (by simpa [advanceResult] using ht)
    refine ⟨jet::jets,?_,(6*(nodes start).length+4+(c+1))+u+1,?_,r3,?_,?_⟩
    · simpa only [List.range'_succ] using List.Forall₂.cons hjet hjets
    · simp only [loopBound]
      omega
    · exact (parserRegs_frame regs true true (regs 39)).trans
        ((parserRegs_frame r0 false true (r0 39)).trans (hcf.trans hrf))
    · have hguard : (ready regs s (nodeSamples nodes) start (count+1)).regs 37 = true := by
        simp [ready,state,parserRegs]
      have hbody := hread.seq (hcall'.seq hpop)
      simpa only [loop,finishLoop] using Eval.while_true hguard hbody hrest

theorem loopBound_eq_sum (nodes : ℕ → List Bool) (cost : ℕ → ℕ)
    (maxJet start count : ℕ) :
    loopBound nodes cost maxJet start count =
      ((List.range' start count).map (fun i => cost i+16*(nodes i).length+3*maxJet+22)).sum+1 := by
  induction count generalizing start with
  | zero => simp [loopBound]
  | succ count ih =>
    simp only [loopBound,callbackBound,List.range'_succ,List.map_cons,List.sum_cons,ih]
    omega

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
