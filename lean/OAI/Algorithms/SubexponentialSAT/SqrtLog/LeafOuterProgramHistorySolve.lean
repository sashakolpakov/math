import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSolve
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashHistory

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls HashSelectProgram

theorem solve_history_eval {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (mass acceptedCount : Cmd 40 896) (a : Data) (initial : Records)
    (width B C cost countCost countBits : ℕ) (seed : List Bool) (rest : Records)
    (score : Records → List Bool → List Bool) (valid : Records → List Bool → Prop)
    (hw : WorkerEmpty a)
    (hr : Execution.HashInputs.Ready (projectState selector.register selector.stack a))
    (hrows : a.stacks 777=candidateEncoding initial)
    (hfamily : generatedPayloads (SubexpAlphabetProgram.alphabetWords (a.stacks 768))
      (CounterPrograms.value (a.stacks 773))=seed::rest)
    (hmass : ∀ frame, Execution.Hash.ContextFrame selector a frame →
      ∀ round < CounterPrograms.value (a.stacks 774), ∀ state,
      ControllerReady selector.controller frame (seed::rest)
        (iter (payloadNext score seed rest) round initial) state →
      MassSpec mass selector.controller.trial.core (afterCopyFamily selector.controller.trial state)
        (score (iter (payloadNext score seed rest) round initial))
        (valid (iter (payloadNext score seed rest) round initial)) B C cost)
    (hp : ∀ round < CounterPrograms.value (a.stacks 774), ∀ bits ∈ seed::rest,
      valid (iter (payloadNext score seed rest) round initial) bits ∧ bits.length ≤ C ∧
        (score (iter (payloadNext score seed rest) round initial) bits).length=B)
    (hmodels : ∀ x, HashSelect.accepts (HashSelect.cnfRowAccept clauses)
      ((iter (payloadNext score seed rest) (CounterPrograms.value (a.stacks 774)) initial).map
        (HashFamilyPayload.decodeVariableRow m width)) x=true ↔ ∀ e, (clauses e).eval x=true)
    (hcount : ∀ b : Data, Execution.Hash.ContextFrame selector a b → WorkerEmpty b →
      b.stacks 777=candidateEncoding (iter (payloadNext score seed rest)
        (CounterPrograms.value (a.stacks 774)) initial) →
      ∃ t ≤ countCost, ∃ c : Data, Eval acceptedCount t b c ∧ c.stacks 787=[] ∧
        (c.stacks 788).length ≤ countBits ∧
        BinaryArithmetic.toNat (c.stacks 788)=HashSelect.acceptedCount (HashSelect.cnfRowAccept clauses)
          ((iter (payloadNext score seed rest) (CounterPrograms.value (a.stacks 774)) initial).map
            (HashFamilyPayload.decodeVariableRow m width))) :
    ∃ steps b bit, Eval (solve mass acceptedCount) steps a b ∧
      steps ≤ Execution.Hash.budget (a.stacks 768) (a.stacks 773) (a.stacks 774) B C cost+
        countCost+5*countBits+11 ∧ b.stacks 787=[bit] ∧
      (bit=true ↔ ∃ x, ∀ e, (clauses e).eval x=true) := by
  obtain ⟨th,hth,b,heh,hbr,_,hbf⟩ := Execution.Hash.command_eval_history selector mass a initial score valid
    B C cost seed rest hr hrows hfamily hmass hp
  have hbw : WorkerEmpty b := selected_worker_empty hw hbf
  obtain ⟨tc,htc,c,hec,hc787,hcl,hcv⟩ := hcount b hbf hbw hbr
  obtain ⟨td,d,bit,hed,htd,hd787,_,hsat,_⟩ := finish_eval clauses _ c hc787 hcv hmodels
  refine ⟨th+(tc+td),d,bit,heh.seq (hec.seq hed),?_,hd787,hsat⟩
  change th ≤ Execution.Hash.budget (a.stacks 768) (a.stacks 773) (a.stacks 774) B C cost at hth
  omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
