import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCandidateProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFFirstWitness
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareProgram

namespace OAI.Algorithms

/-! The actual tuple callback: prepare a candidate, check it, and retain the
first accepted witness on an outside stack. -/

namespace SubexponentialSAT.ExecSunflowerCallback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Clause := List (List Bool)
abbrev Formula := List Clause
abbrev Data := State 32 32
abbrev Code := Cmd 32 32

def checkReg (i : Fin 18) : Fin 32 := Fin.castAdd 14 i
def checkStack (i : Fin 16) : Fin 32 := Fin.castAdd 16 i
theorem checkReg_injective : Function.Injective checkReg := Fin.castAdd_injective 18 14
theorem checkStack_injective : Function.Injective checkStack := Fin.castAdd_injective 16 16

def check : Code := .call (ProgramLinking.liftProgram
  ExecSunflowerCandidateProgram.program checkReg checkStack)

theorem check_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : ExecSunflowerCandidateProgram.Ready G H width size
      (projectState checkReg checkStack d)) :
    ∃ n ≤ ExecSunflowerCandidateProgram.bound G H width size + 1, ∃ e : Data,
      Eval check n d e ∧
      e.stacks = Function.update d.stacks 12 [ExecSunflowerCandidateProgram.answer G H width size] ∧
      e.regs 17 = ExecSunflowerCandidateProgram.answer G H width size := by
  let a := projectState checkReg checkStack d
  obtain ⟨b, ⟨n, hn, ht⟩, hb, ha⟩ := ExecSunflowerCandidateProgram.program_run G H width size a hi
  let e := embedState checkReg checkStack d b
  have he : Eval check n d e :=
    eval_call_from_state _ checkReg checkStack d checkReg_injective checkStack_injective ht
  have hs : e.stacks = Function.update d.stacks 12
      [ExecSunflowerCandidateProgram.answer G H width size] := by
    change Function.extend checkStack b.stacks d.stacks = _
    rw [hb, ProgramLinking.extend_update checkStack_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project checkReg checkStack d checkReg_injective checkStack_injective)
    change Function.extend checkStack a.stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl
  exact ⟨n, hn, e, he, hs,
    (embedState_register checkReg checkStack d b checkReg_injective 17).trans ha⟩

theorem witness_stacks (d : Data) :
    (ExecCNFFirstWitness.result d).stacks = Function.update d.stacks 21
      (ExecCNFFirstWitness.save (d.stacks 17) (d.stacks 21) (d.regs 17)) := by
  funext i
  by_cases h : i = 21
  · subst i
    simpa using ExecCNFFirstWitness.result_witness d
  · simpa [h] using ExecCNFFirstWitness.result_stack_frame d i h

def discard : Code := .ite 17 (.base .skip)
  (.seq (ExecCNFTupleSplit.clear 13) (ExecCNFTupleSplit.clear 8))

def discarded (d : Data) : Data :=
  if d.regs 17 then d else ExecCNFTupleSplit.cleared 8 (ExecCNFTupleSplit.cleared 13 d)

def discardCost (d : Data) : ℕ :=
  if d.regs 17 then 1 else 2 * (d.stacks 13).length + 2 * (d.stacks 8).length + 7

theorem discard_eval (d : Data) : Eval discard (discardCost d) d (discarded d) := by
  cases ha : d.regs 17 with
  | true =>
      simpa [discard, discardCost, discarded, ha] using
        (Eval.ite_true (yes := .base .skip)
          (no := .seq (ExecCNFTupleSplit.clear 13) (ExecCNFTupleSplit.clear 8)) ha
          (Eval.base (StructuredProgram.Eval.skip d)))
  | false =>
      have hc := Eval.seq (ExecCNFTupleSplit.clear_eval 13 d)
        (ExecCNFTupleSplit.clear_eval 8 (ExecCNFTupleSplit.cleared 13 d))
      have ht := Eval.ite_false (test := 17) (yes := .base .skip) ha hc
      convert ht using 1 <;>
        simp [discard, discardCost, discarded, ha, ExecCNFTupleSplit.cleared,
          StackRoutines.clearStacks] ; omega

def checkCommit : Code := .seq check (.seq ExecCNFFirstWitness.command
  (.seq discard (ExecCNFTupleSplit.clear 12)))

def stageBound (G : Formula) (H : Clause) (width size tuple : List Bool) : ℕ :=
  ExecSunflowerCandidateProgram.bound G H width size + 7 * tuple.length +
    2 * (Encoding.encodeList (Encoding.encodeList id) G).length +
    2 * (Encoding.encodeList id H).length + 21

def stageStacks (G : Formula) (H : Clause) (width size : List Bool) (d : Data) :
    Fin 32 → List Bool :=
  if ExecSunflowerCandidateProgram.answer G H width size then
    Function.update d.stacks 21 (d.stacks 17)
  else Function.update (Function.update d.stacks 13 []) 8 []

theorem checkCommit_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : ExecSunflowerCandidateProgram.Ready G H width size
      (projectState checkReg checkStack d))
    (h21 : d.stacks 21 = []) (h25 : d.stacks 25 = []) :
    ∃ n ≤ stageBound G H width size (d.stacks 17), ∃ e : Data,
      Eval checkCommit n d e ∧ e.stacks = stageStacks G H width size d := by
  obtain ⟨n, hn, e, he, hs, ha⟩ := check_eval G H width size d hi
  have he25 : e.stacks 25 = [] := by simp [hs, h25]
  have he21 : e.stacks 21 = [] := by simp [hs, h21]
  let w := ExecCNFFirstWitness.result e
  let q := discarded w
  let result := ExecCNFTupleSplit.cleared 12 q
  have hw17 : w.regs 17 = ExecSunflowerCandidateProgram.answer G H width size :=
    (ExecCNFFirstWitness.result_register_frame e 17 (by decide) (by decide)).trans ha
  have hws := witness_stacks e
  have he12 : e.stacks 12 = [ExecSunflowerCandidateProgram.answer G H width size] := by simp [hs]
  have hw12 : w.stacks 12 = [ExecSunflowerCandidateProgram.answer G H width size] := by
    simpa [w, hws] using he12
  have hq12 : q.stacks 12 = [ExecSunflowerCandidateProgram.answer G H width size] := by
    cases hv : w.regs 17 <;>
      simp [q, discarded, hv, ExecCNFTupleSplit.cleared, StackRoutines.clearStacks, hw12]
  have hw13 : w.stacks 13 = Encoding.encodeList (Encoding.encodeList id) G := by
    have h := hi.1
    change d.stacks (checkStack 13) = Encoding.encodeList (Encoding.encodeList id) G at h
    simpa [w, hws, hs, checkStack] using h
  have hw8 : w.stacks 8 = Encoding.encodeList id H := by
    have h := hi.2.1
    change d.stacks (checkStack 8) = Encoding.encodeList id H at h
    simpa [w, hws, hs, checkStack] using h
  have hwcost := ExecCNFFirstWitness.cost_le e
  have hdcost : discardCost w ≤
      2 * (Encoding.encodeList (Encoding.encodeList id) G).length +
        2 * (Encoding.encodeList id H).length + 7 := by
    unfold discardCost
    split <;> simp [hw13, hw8]
  refine ⟨n + (ExecCNFFirstWitness.cost e +
    (discardCost w + (2 * (q.stacks 12).length + 3))), ?_, result, ?_, ?_⟩
  · rw [hq12]
    simp only [List.length_cons, List.length_nil]
    have he17 : e.stacks 17 = d.stacks 17 := by simp [hs]
    rw [he17] at hwcost
    unfold stageBound
    omega
  · exact Eval.seq he (Eval.seq (ExecCNFFirstWitness.command_eval e he25)
      (Eval.seq (discard_eval w) (ExecCNFTupleSplit.clear_eval 12 q)))
  · have hd12 : d.stacks 12 = [] := hi.2.2.2.2 12 (by decide)
    funext i
    cases hacc : ExecSunflowerCandidateProgram.answer G H width size <;>
      simp [stageStacks, hacc, result, q, discarded, hw17, w, witness_stacks,
        ExecCNFFirstWitness.save, he21, ha, hs, ExecCNFTupleSplit.cleared,
        StackRoutines.clearStacks, Function.update_apply] <;>
      split_ifs <;> subst_vars <;> simp_all

def WorkspaceEmpty (d : Data) : Prop :=
  ∀ i : Fin 13, i ≠ 8 → d.stacks (Fin.castAdd 19 i) = []

def Fresh (F : Formula) (mask limit width size : List Bool) (words : List (List Bool))
    (d : Data) : Prop :=
  CandidatePrepareProgram.Ready F mask limit words d ∧ WorkspaceEmpty d ∧
    d.stacks 14 = width ∧ d.stacks 15 = size ∧ d.stacks 21 = []

def accepted (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) : Bool :=
  CandidatePrepareProgram.valid limit words &&
    ExecSunflowerCandidateProgram.answer (CandidatePrepareProgram.selected F words)
      (CandidatePrepareProgram.core F mask words) width size

def freshStacks (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) : Fin 32 → List Bool :=
  if accepted F mask limit width size words then
    Function.update (Function.update (Function.update d.stacks 13
      (CandidatePrepareProgram.formulaCode (CandidatePrepareProgram.selected F words))) 8
      (CandidatePrepareProgram.clauseCode (CandidatePrepareProgram.core F mask words)))
      21 (d.stacks 17)
  else d.stacks

def freshCommand : Code := .seq CandidatePrepareProgram.command
  (.ite 30 checkCommit (.base .skip))

def bound (F : Formula) (mask limit width size : List Bool) (words : List (List Bool)) : ℕ :=
  CandidatePrepareProgram.bound F mask limit words +
    stageBound (CandidatePrepareProgram.selected F words) (CandidatePrepareProgram.core F mask words)
      width size (CandidatePrepareProgram.tupleCode (mask :: words)) + 3

theorem freshCommand_eval (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) (h : Fresh F mask limit width size words d) :
    ∃ n, n + 2 ≤ bound F mask limit width size words ∧ ∃ e : Data,
      Eval freshCommand n d e ∧ e.stacks = freshStacks F mask limit width size words d := by
  rcases h with ⟨hprep, hwork, hwidth, hsize, h21⟩
  obtain ⟨np, hnp, p, hep, hps, hp30⟩ :=
    CandidatePrepareProgram.command_eval F mask limit words d hprep
  obtain ⟨hF, ht, hl, hw, h8, h13, h22, h23, h24, h25, h26⟩ := hprep
  cases hv : CandidatePrepareProgram.valid limit words with
  | false =>
      have hbranch : Eval (.ite 30 checkCommit (.base .skip)) 1 p p :=
        Eval.ite_false (hp30.trans hv) (.base (.skip p))
      refine ⟨np + 1, ?_, p, Eval.seq hep hbranch, ?_⟩
      · unfold bound
        omega
      · funext i
        simp [hps, CandidatePrepareProgram.outputStacks, freshStacks, accepted, hv,
          Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
  | true =>
      have hi : ExecSunflowerCandidateProgram.Ready
          (CandidatePrepareProgram.selected F words) (CandidatePrepareProgram.core F mask words)
          width size (projectState checkReg checkStack p) := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [projectState, checkStack, hps, CandidatePrepareProgram.outputStacks, hv,
            CandidatePrepareProgram.formulaCode, CandidatePrepareProgram.clauseCode] ; rfl
        · simp [projectState, checkStack, hps, CandidatePrepareProgram.outputStacks, hv,
            CandidatePrepareProgram.clauseCode]
        · simpa [projectState, checkStack, hps, CandidatePrepareProgram.outputStacks] using hwidth
        · simpa [projectState, checkStack, hps, CandidatePrepareProgram.outputStacks] using hsize
        · intro i hi
          have he := hwork i hi
          fin_cases i <;> first
          | exact False.elim (hi rfl)
          | simpa [projectState, checkStack, hps,
              CandidatePrepareProgram.outputStacks] using he
      have hp21 : p.stacks 21 = [] := by simp [hps, CandidatePrepareProgram.outputStacks, h21]
      have hp25 : p.stacks 25 = [] := by simp [hps, CandidatePrepareProgram.outputStacks, h25]
      obtain ⟨nc, hnc, e, hec, hes⟩ := checkCommit_eval
        (CandidatePrepareProgram.selected F words) (CandidatePrepareProgram.core F mask words)
        width size p hi hp21 hp25
      have hbranch : Eval (.ite 30 checkCommit (.base .skip)) (nc + 1) p e :=
        Eval.ite_true (hp30.trans hv) hec
      refine ⟨np + (nc + 1), ?_, e, Eval.seq hep hbranch, ?_⟩
      · have hpt : p.stacks 17 = CandidatePrepareProgram.tupleCode (mask :: words) := by
          simp [hps, CandidatePrepareProgram.outputStacks, ht]
        rw [hpt] at hnc
        unfold bound
        omega
      · funext i
        rw [hes]
        cases ha : ExecSunflowerCandidateProgram.answer (CandidatePrepareProgram.selected F words)
            (CandidatePrepareProgram.core F mask words) width size <;>
          simp [stageStacks, freshStacks, accepted, hv, ha, hps,
            CandidatePrepareProgram.outputStacks, Function.update_apply] ;
          split_ifs <;> subst_vars <;> simp_all

def command : Code := .seq ExecCNFFirstWitness.peek
  (.ite 1 (.base .skip) freshCommand)

def outputStacks (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) : Fin 32 → List Bool :=
  if d.stacks 21 = [] then freshStacks F mask limit width size words d else d.stacks

/-- The callback skips all preparation once a witness exists. On the remaining
path, every parser, guard, selected-clause scan and cleanup is actually run. -/
theorem command_eval (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data)
    (h : d.stacks 21 = [] → Fresh F mask limit width size words d) :
    ∃ n ≤ bound F mask limit width size words, ∃ e : Data,
      Eval command n d e ∧ e.stacks = outputStacks F mask limit width size words d := by
  have hpeek : Eval ExecCNFFirstWitness.peek 1 d (ExecCNFFirstWitness.peeked d) :=
    .base (.atom _ _)
  by_cases hw : d.stacks 21 = []
  · have hp : (ExecCNFFirstWitness.peeked d).regs 1 = false := by simp [hw]
    have hf : Fresh F mask limit width size words (ExecCNFFirstWitness.peeked d) := h hw
    obtain ⟨n, hn, e, he, hs⟩ := freshCommand_eval F mask limit width size words
      (ExecCNFFirstWitness.peeked d) hf
    refine ⟨1 + (n + 1), by omega, e, Eval.seq hpeek (Eval.ite_false hp he), ?_⟩
    simpa [outputStacks, hw, freshStacks] using hs
  · have hp : (ExecCNFFirstWitness.peeked d).regs 1 = true := by
      simp only [ExecCNFFirstWitness.peeked_present]
      cases hs : d.stacks 21 <;> simp_all
    refine ⟨2, ?_, ExecCNFFirstWitness.peeked d,
      Eval.seq hpeek (Eval.ite_true hp (.base (.skip _))), ?_⟩
    · unfold bound
      omega
    · simp [outputStacks, hw]

def program := compiled command 17 21

theorem program_run (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data)
    (h : d.stacks 21 = [] → Fresh F mask limit width size words d) :
    ∃ e : Data, RunsIn program (bound F mask limit width size words + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = outputStacks F mask limit width size words d := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval F mask limit width size words d h
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 17 21⟩, hs⟩

theorem primitive_run (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data)
    (h : d.stacks 21 = [] → Fresh F mask limit width size words d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (bound F mask limit width size words + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks = outputStacks F mask limit width size words d := by
  obtain ⟨e, ht, hs⟩ := program_run F mask limit width size words d h
  exact ⟨e, BitProgram.primitive_execution program ht, hs⟩

/-- This invariant omits the tuple and odometer scratch stacks, and all
registers. After success the callback simply preserves the saved witness. -/
def Invariant (F : Formula) (limit width size : List Bool) (d : Data) : Prop :=
  d.stacks 21 = [] → d.stacks 16 = CandidatePrepareProgram.formulaCode F ∧
    d.stacks 19 = limit ∧ CandidatePrepareProgram.WorkEmpty d ∧ WorkspaceEmpty d ∧
    d.stacks 14 = width ∧ d.stacks 15 = size

theorem fresh_of_invariant (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) (hi : Invariant F limit width size d)
    (ht : d.stacks 17 = CandidatePrepareProgram.tupleCode (mask :: words))
    (hw : d.stacks 21 = []) : Fresh F mask limit width size words d := by
  obtain ⟨hF, hL, hwork, hworkspace, hwidth, hsize⟩ := hi hw
  exact ⟨⟨hF, ht, hL, hwork⟩, hworkspace, hwidth, hsize, hw⟩

theorem outputStacks_frame (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) (i : Fin 32)
    (h8 : i ≠ 8) (h13 : i ≠ 13) (h21 : i ≠ 21) :
    outputStacks F mask limit width size words d i = d.stacks i := by
  unfold outputStacks freshStacks
  split_ifs <;> simp [h8, h13, h21]

theorem outputStacks_witness (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) :
    outputStacks F mask limit width size words d 21 =
      ExecCNFFirstWitness.save (d.stacks 17) (d.stacks 21)
        (accepted F mask limit width size words) := by
  by_cases hw : d.stacks 21 = [] <;>
    cases ha : accepted F mask limit width size words <;>
    simp [outputStacks, freshStacks, ExecCNFFirstWitness.save, hw, ha]

theorem outputStacks_eq_of_no_witness (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d : Data) (ht : d.stacks 17 ≠ [])
    (hw : outputStacks F mask limit width size words d 21 = []) :
    outputStacks F mask limit width size words d = d.stacks := by
  by_cases h21 : d.stacks 21 = []
  · cases ha : accepted F mask limit width size words
    · simp [outputStacks, freshStacks, h21, ha]
    · have he : d.stacks 17 = [] := by
        simpa [outputStacks, freshStacks, h21, ha] using hw
      exact False.elim (ht he)
  · simp [outputStacks, h21]

theorem invariant_preserved (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d e : Data) (hi : Invariant F limit width size d)
    (ht : d.stacks 17 ≠ [])
    (hs : e.stacks = outputStacks F mask limit width size words d) :
    Invariant F limit width size e := by
  intro h21
  have hout : outputStacks F mask limit width size words d 21 = [] := by
    simpa only [hs] using h21
  have heq : e.stacks = d.stacks :=
    hs.trans (outputStacks_eq_of_no_witness F mask limit width size words d ht hout)
  have hold : d.stacks 21 = [] := by simpa only [heq] using h21
  simpa only [CandidatePrepareProgram.WorkEmpty, WorkspaceEmpty, heq] using hi hold

end SubexponentialSAT.ExecSunflowerCallback

end OAI.Algorithms
