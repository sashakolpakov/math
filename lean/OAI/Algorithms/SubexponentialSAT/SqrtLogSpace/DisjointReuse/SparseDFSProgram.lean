import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSBoundarySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointSparsifyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseControllerProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

abbrev Data := State 80 1220
abbrev Code := Cmd 80 1220

def registers (r : ℕ) (hr : r ≤ 80) : Fin r ↪ Fin 80 := Fin.castLEEmb hr

def selectorStack : Fin 24 ↪ Fin 1220 :=
  (Fin.castLEEmb (by decide : 24 ≤ 31)).trans SparseDFSBoundarySpace.rootEmbedding

def frontierStack : Fin 4 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.popStack.trans SparseDFSBoundarySpace.rootEmbedding

def pairStack : Fin 5 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.pairStack.trans SparseDFSBoundarySpace.rootEmbedding

def countStack : Fin 3 ↪ Fin 1220 :=
  SparseDFSBoundarySpace.countStack.trans SparseDFSBoundarySpace.rootEmbedding

/-- The splitter keeps the threshold outside its entire local footprint. -/
def splitterView : Fin 23 ↪ Fin 31 where
  toFun := ![24, 25, 26, 27, 13, 9, 12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 14, 15, 16, 17, 18]
  inj' := by decide

def splitterStack : Fin 23 ↪ Fin 1220 :=
  splitterView.trans SparseDFSBoundarySpace.rootEmbedding

def startFrontier : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack)

def popCurrent : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack)

def selectCurrent (k : ℕ) : Code :=
  .call (ProgramLinking.liftProgram (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack)

def splitCurrent : Code :=
  .call (ProgramLinking.liftProgram DisjointBranchProgram.program
    (registers 15 (by decide)) splitterStack)

def pushChildren : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack)

def accumulate : Code :=
  .call (ProgramLinking.liftProgram SparseCountProgram.Accumulator.program
    (registers 8 (by decide)) countStack)

def clearPort (port : Fin 1220) : Code :=
  .call (StackRoutines.clearProgram port 0 1)

/-- The finite list is part of the instruction table, never a stored work list. -/
def clearPorts : List (Fin 1220) → Code
  | [] => .base .skip
  | port :: rest => .seq (clearPort port) (clearPorts rest)

private opaque lowPortsWrapped :
    {ports : List (Fin 1220) //
      ports = (List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220))} :=
  ⟨(List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220)), rfl⟩

/-- The fixed low-workspace ports, kept opaque to avoid reducing the entire
256-element instruction table during routine typeclass and theorem checking. -/
def lowPorts : List (Fin 1220) := lowPortsWrapped.1

theorem lowPorts_eq :
    lowPorts = (List.finRange 256).map (Fin.castLE (by decide : 256 ≤ 1220)) :=
  lowPortsWrapped.2

def clearLow : Code := clearPorts lowPorts

/-- Every iteration re-reads the physical pending tag after all callbacks. -/
def testPending : Code := .base (.atom (.peek 257 2 1))

/-- The total stack is empty on entry and becomes canonical binary zero. -/
def startTotal : Code :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 260 0)))

def branch : Code := .seq splitCurrent pushChildren

/-- Explicitly discard the current body and every low workspace port before
retesting the frontier. No callback cleanup or register persistence is implicit. -/
def finishVisit : Code :=
  .seq (clearPort 265) (.seq clearLow testPending)

/-- `leaf` includes the actual charged leaf loaders, computation, result
export to stack263, and cleanup. It must preserve the persistent outer frame. -/
def body (k : ℕ) (leaf : Code) : Code :=
  .seq popCurrent
    (.seq (selectCurrent k)
      (.seq (.ite 23 branch (.seq leaf accumulate)) finishVisit))

def loop (k : ℕ) (leaf : Code) : Code := .while 2 (body k leaf)

/-- Physically clear the external word and copy scratch before preserving bit
order in the final canonical output. Retained raw input is charged here. -/
def exportCount : Code :=
  .seq (clearPort 0) (.seq (clearPort 256)
    (.call (StackRoutines.copyProgram 260 256 0 0 1)))

/-- This command starts from an already normalized current body, saved original
header and chosen threshold. Preprocessing is charged in the caller. -/
def command (k : ℕ) (leaf : Code) : Code :=
  .seq startFrontier
    (.seq startTotal (.seq testPending (.seq (loop k leaf) exportCount)))

def program (k : ℕ) (leaf : Code) := compiled (command k leaf) 256 256

theorem testPending_eval (d : Data) :
    Eval testPending 1 d
      ⟨readRegs d.regs 2 1 (d.stacks 257).head?, d.stacks⟩ := by
  simpa [testPending, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr]
    using Eval.base (StructuredProgram.Eval.atom (.peek (257 : Fin 1220) (2 : Fin 80) 1) d)

theorem testPending_tag (d : Data) (tag : Bool) (tail : List Bool)
    (hpending : d.stacks 257 = tag :: tail) :
    ∃ e, Eval testPending 1 d e ∧ e.regs 2 = tag ∧ e.stacks = d.stacks := by
  refine ⟨_, testPending_eval d, ?_, rfl⟩
  simp [hpending, readRegs]

theorem startTotal_eval (d : Data) (htotal : d.stacks 260 = []) :
    Eval startTotal 2 d
      ⟨Function.update d.regs 0 false, Function.update d.stacks 260 [false]⟩ := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 80) false) d).seq
    (StructuredProgram.Eval.atom (.push (260 : Fin 1220) (0 : Fin 80)) _)
  simpa [startTotal, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, htotal]
    using Eval.base h

theorem clearPort_eval (port : Fin 1220) (d : Data) :
    Eval (clearPort port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run port 0 1 d.regs d.stacks)

theorem clearPorts_eval (ports : List (Fin 1220)) (d : Data) (bound : ℕ)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * ports.length, ∃ e,
      Eval (clearPorts ports) t d e ∧
      (∀ i ∈ ports, e.stacks i = []) ∧
      (∀ i, i ∉ ports → e.stacks i = d.stacks i) ∧
      (∀ i, (e.stacks i).length ≤ bound) := by
  induction ports generalizing d with
  | nil => exact ⟨0, by simp, d, .base (.skip d), by simp, by simp, hbound⟩
  | cons port rest ih =>
    let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩
    have habound : ∀ i, (a.stacks i).length ≤ bound := by
      intro i
      by_cases hi : i = port
      · subst i
        simp [a, StackRoutines.clearStacks]
      · simpa [a, StackRoutines.clearStacks, hi] using hbound i
    obtain ⟨t, ht, e, he, hclear, hframe, hbe⟩ := ih a habound
    refine ⟨2 * (d.stacks port).length + 3 + t, ?_, e,
      (clearPort_eval port d).seq he, ?_, ?_, hbe⟩
    · have hd := hbound port
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with hi | hi
      · subst i
        by_cases hp : port ∈ rest
        · exact hclear port hp
        · rw [hframe port hp]
          simp [a, StackRoutines.clearStacks]
      · exact hclear i hi
    · intro i hi
      have hir : i ∉ rest := fun hir => hi (List.mem_cons_of_mem _ hir)
      have hip : i ≠ port := fun heq => hi (by simp [heq])
      rw [hframe i hir]
      simp [a, StackRoutines.clearStacks, hip]

theorem mem_lowPorts (i : Fin 1220) : i ∈ lowPorts ↔ i.val < 256 := by
  rw [lowPorts_eq]
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem clearLow_eval (d : Data) (bound : ℕ)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 256, ∃ e,
      Eval clearLow t d e ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧
      (∀ i, 256 ≤ i.val → e.stacks i = d.stacks i) ∧
      (∀ i, (e.stacks i).length ≤ bound) := by
  obtain ⟨t, ht, e, he, hc, hf, hb⟩ := clearPorts_eval lowPorts d bound hbound
  refine ⟨t, by simpa [lowPorts_eq] using ht, e, he, ?_, ?_, hb⟩
  · intro i hi
    exact hc i ((mem_lowPorts i).mpr hi)
  · intro i hi
    exact hf i (by rw [mem_lowPorts]; omega)

theorem exportCount_eval (d : Data) :
    ∃ e, Eval exportCount
      (2 * (d.stacks 0).length + 2 * (d.stacks 256).length +
        7 * (d.stacks 260).length + 11) d e ∧
      e.stacks 256 = d.stacks 260 ∧ e.stacks 0 = [] ∧
      ∀ i, i ≠ 0 → i ≠ 256 → e.stacks i = d.stacks i := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 0 d.stacks⟩
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 256 a.stacks⟩
  have h0 : b.stacks 0 = [] := by simp [b, a, StackRoutines.clearStacks]
  have hout : b.stacks 256 = [] := by simp [b, StackRoutines.clearStacks]
  have htotal : b.stacks 260 = d.stacks 260 := by
    simp [b, a, StackRoutines.clearStacks]
  have h256 : a.stacks 256 = d.stacks 256 := by simp [a, StackRoutines.clearStacks]
  have hcopy : Eval (.call (StackRoutines.copyProgram 260 256 0 0 1))
      (7 * (b.stacks 260).length + 5) b
      ⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 260 256 b.stacks⟩ :=
    Eval.call _ (ListRegisterProgram.copy_run (r := 80) (s := 1220)
      260 256 0 0 1 (by decide) (by decide) (by decide) (by decide) b.regs b.stacks h0)
  have hrun := (clearPort_eval 0 d).seq ((clearPort_eval 256 a).seq hcopy)
  refine ⟨⟨readRegs b.regs 0 1 none, StackRoutines.copyStacks 260 256 b.stacks⟩,
    ?_, ?_, ?_, ?_⟩
  · convert hrun using 1
    · rfl
    · simp [htotal, h256]
      omega
  · simp [StackRoutines.copyStacks, hout, htotal]
  · simp [StackRoutines.copyStacks, h0]
  · intro i hi0 hi256
    simp [StackRoutines.copyStacks, b, a, StackRoutines.clearStacks, hi0, hi256]

/-- Output cleanup and copying use only their own linear work, never the
exponentially long traversal time; every one of the 1220 stacks is counted. -/
theorem exportCount_prefix_space (d : Data) (n bound : ℕ)
    (hcount : (d.stacks 260).length ≤ n + 1)
    (hframe : ∀ i, (d.stacks i).length ≤ bound)
    (prefixSteps : ℕ)
    (c : Cfg 80 1220 (size exportCount + 1))
    (ht : prefixSteps ≤ 2 * (d.stacks 0).length + 2 * (d.stacks 256).length +
      7 * (d.stacks 260).length + 12)
    (hc : Trace (compiled exportCount 256 256) prefixSteps
      (d.withPC (some (compiled exportCount 256 256).entry)) c) :
    dataBits c ≤ 1224 * bound + 7 * n + 19 := by
  have hsum : stackBits d.stacks ≤ 1220 * bound := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hframe i)
    simpa only [stackBits, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] using h
  have h0 := hframe 0
  have hout := hframe 256
  have hg := trace_dataBits (compiled exportCount 256 256) hc
  change dataBits c ≤ stackBits d.stacks + prefixSteps at hg
  omega

/-- Once concrete phase executions are proved, this is the exact branch trace
of the already defined body; the found flag is consumed immediately. -/
theorem body_branch_eval {k : ℕ} {leaf : Code} {a b c d e : Data}
    {tpop tselect tbranch tfinish : ℕ}
    (hpop : Eval popCurrent tpop a b)
    (hselect : Eval (selectCurrent k) tselect b c)
    (hfound : c.regs 23 = true) (hbranch : Eval branch tbranch c d)
    (hfinish : Eval finishVisit tfinish d e) :
    Eval (body k leaf) (tpop + (tselect + (tbranch + 1 + tfinish))) a e :=
  hpop.seq (hselect.seq ((Eval.ite_true hfound hbranch).seq hfinish))

theorem body_leaf_eval {k : ℕ} {leaf : Code} {a b c d e f : Data}
    {tpop tselect tleaf tadd tfinish : ℕ}
    (hpop : Eval popCurrent tpop a b)
    (hselect : Eval (selectCurrent k) tselect b c)
    (hmissing : c.regs 23 = false) (hleaf : Eval leaf tleaf c d)
    (hadd : Eval accumulate tadd d e) (hfinish : Eval finishVisit tfinish e f) :
    Eval (body k leaf) (tpop + (tselect + (tleaf + tadd + 1 + tfinish))) a f :=
  hpop.seq (hselect.seq ((Eval.ite_false hmissing (hleaf.seq hadd)).seq hfinish))

theorem splitter_pair_projection (frame : Data) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    projectState (registers 4 (by decide)) pairStack
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)) =
      ExecWorklistProgram.data false false false false pending header
        (ExecWorklistProgram.record
          (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)))
        (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
          (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H))) := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 0
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 1
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 2
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 3
  · funext i
    fin_cases i
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 0
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 1
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 2
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 3
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 7

theorem branch_execution (frame : Data) (regs : Fin 15 → Bool)
    (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      ∃ e, Eval branch t
        (embedState (registers 15 (by decide)) splitterStack frame
          (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
        e.stacks 257 =
          ExecWorklistProgram.record
            (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
            (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ pending) ∧
        e.stacks 258 = header ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = frame.stacks 259 ∧
        e.stacks 260 = frame.stacks 260 := by
  let left := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let right := ExecCoreChildProgram.formulaCode
    (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)
  let middle := embedState (registers 15 (by decide)) splitterStack frame
    (DisjointBranchProgram.outputState pending header F S H)
  obtain ⟨t, ht, hs⟩ := DisjointBranchProgram.program_runsIn regs pending header F S H
  have hsplit : Eval splitCurrent t
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) middle :=
    eval_call_lifted DisjointBranchProgram.program (registers 15 (by decide))
      splitterStack frame (registers 15 (by decide)).injective splitterStack.injective hs
  have hpair := SparseFrontierProgram.pushPair_trace left right header pending
    false false false false
  rw [← splitter_pair_projection frame pending header F S H] at hpair
  have hp := eval_call_from_state SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle (registers 4 (by decide)).injective
    pairStack.injective hpair
  refine ⟨t + (13 * right.length + 13 * left.length + 37), ?_, _, hsplit.seq hp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl := ExecCoreChildProgram.result_length_le F S H
    have hr := DisjointBranchProgram.resultB_length_le F S H
    have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
      unfold ExecCoreChildProgram.inputVolume
      omega
    have hla : left.length ≤ ExecCoreChildProgram.inputVolume F S H := by
      dsimp [left]
      unfold ExecCoreChildProgram.inputVolume
      omega
    dsimp [right] at hr ⊢
    nlinarith only [ht, hr, hla, hv]
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 0
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 1
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 2
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 3
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 265 (by decide)]
    exact embedState_stack (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 4
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 259 (by decide)]
    exact embedState_stack_frame (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) 259 (by decide)
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 260 (by decide)]
    exact embedState_stack_frame (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) 260 (by decide)



theorem splitter_input_projection (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hscratch : ∀ i : Fin 23, 7 ≤ i.val → d.stacks (splitterStack i) = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · rfl
    · rfl
    · exact hleft
    · exact hright
    · exact hF
    · exact hH
    · exact hS
  · simpa [ExecBranchControllerSupport.emptyBank] using
      hscratch (Fin.natAdd 7 j) (by simp)

theorem splitter_input_projection_of_clean (d : Data)
    (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply splitter_input_projection d F S H hF hH hS hleft hright
  intro i hi
  have hrange : (splitterStack i).val < 24 ∧ splitterStack i ≠ 9 ∧ splitterStack i ≠ 12 := by
    have h : ∀ j : Fin 23, 7 ≤ j.val →
        (splitterStack j).val < 24 ∧ splitterStack j ≠ 9 ∧ splitterStack j ≠ 12 := by decide
    exact h i hi
  exact hclean _ hrange.1 hrange.2.1 hrange.2.2


/- The typed count identity for the concrete disjoint branch. -/
/-- The physical selector filter accumulates its records in reverse order.
Only the selected finite family matters, and the variable type stays `Fin n`. -/
theorem raw_branch_count_reverse {n k M c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n))) (hpriority : SparsePriorityProgram.RawPriority k F M c H)
    (hnodup : ∀ C ∈ F, C.Nodup) :
    rawCount F =
      rawCount (ExecCoreChildProgram.result F (SparsePriorityProgram.selectedRaw F c H).reverse H) +
      rawCount
        (DisjointBranchProgram.resultB SAT.Literal.negate F (SparsePriorityProgram.selectedRaw F c H).reverse H) := by
  have hc : 2 ≤ c := by
    have hpos := hpriority.core_nonempty
    have hproper := hpriority.core_proper
    omega
  apply DisjointBranchProgram.count_results F (SparsePriorityProgram.selectedRaw F c H).reverse H c hc
  simpa only [ExecCNF.formulaSet, List.map_reverse, List.toFinset_reverse] using
    SparsePriorityProgram.selectedRaw_set F c H hnodup


theorem raw_branch_count {n k M c : ℕ} (F : RawCNF n)
    (H : List (SAT.Literal (Fin n))) (hpriority : SparsePriorityProgram.RawPriority k F M c H)
    (hnodup : ∀ C ∈ F, C.Nodup) :
    rawCount F =
      rawCount (ExecCoreChildProgram.result F (SparsePriorityProgram.selectedRaw F c H) H) +
      rawCount (DisjointBranchProgram.resultB SAT.Literal.negate F (SparsePriorityProgram.selectedRaw F c H) H) := by
  have hc : 2 ≤ c := by
    have hpos := hpriority.core_nonempty
    have hproper := hpriority.core_proper
    omega
  exact DisjointBranchProgram.count_results F (SparsePriorityProgram.selectedRaw F c H) H c hc
    (SparsePriorityProgram.selectedRaw_set F c H hnodup)



theorem branch_execution_from_state (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      ∃ e, Eval branch t d e ∧
        e.stacks 257 =
          ExecWorklistProgram.record
            (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
            (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ d.stacks 257) ∧
        e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
        e.stacks 260 = d.stacks 260 := by
  have hp := splitter_input_projection_of_clean d F S H hF hH hS hleft hright hclean
  have he := branch_execution d (d.regs ∘ registers 15 (by decide))
    (d.stacks 257) (d.stacks 258) F S H
  rw [← hp, embedState_project _ _ d
    (registers 15 (by decide)).injective splitterStack.injective] at he
  exact he


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
