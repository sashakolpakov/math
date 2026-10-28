import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFSubset
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

abbrev Data := State 10 8

abbrev ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def Clean (d : Data) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = []

abbrev copySuffixProgram : Program 10 8 8 := StackRoutines.copyProgram 0 3 7 0 1
abbrev copySuffix : Cmd 10 8 := .call copySuffixProgram
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 0 3 d.stacks⟩

theorem copySuffix_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval copySuffix (7 * (d.stacks 0).length + 5) d (copied d) := by
  apply Eval.call
  simpa [copySuffixProgram, copied, StructuredProgram.State.withPC] using
    ListRegisterProgram.copy_run (r := 10) (s := 8) 0 3 7 0 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp

def emitReg (i : Fin 3) : Fin 10 := if i = 0 then 7 else if i = 1 then 8 else 9
def emitStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 0 else if i = 1 then 7 else if i = 2 then 2 else 1

theorem emitReg_injective : Function.Injective emitReg := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitReg]

theorem emitStack_injective : Function.Injective emitStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [emitStack]

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack
abbrev emitCall : Cmd 10 8 := .call emitProgram

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
      unfold embedState
      congr 1
      · funext i
        by_cases h : ∃ j, reg j = i
        · obtain ⟨j, rfl⟩ := h
          exact hr.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h
      · funext i
        by_cases h : ∃ j, stk j = i
        · obtain ⟨j, rfl⟩ := h
          exact hs.extend_apply _ _ _
        · exact Function.extend_apply' _ _ _ h

theorem emitCall_eval (selected : Bool) (bits : List Bool) (d : Data)
    (hquery : d.stacks 1 = bits.reverse) (hselected : d.regs 9 = selected) :
    ∃ e : Data,
      Eval emitCall (SubexpNormalizeProgram.emitIfSelectedSteps selected bits + 1) d e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ emitStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) selected
      (d.stacks 0) (d.stacks 7) (d.stacks 2) bits.reverse := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg, hselected]
    · funext i
      fin_cases i <;> simp [ emitStack, hquery]
  have ht := SubexpNormalizeProgram.emitIfSelected_trace selected bits
    (d.stacks 0) (d.stacks 7) (d.stacks 2) (d.regs 7) (d.regs 8)
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitReg emitStack d emitReg_injective emitStack_injective ht
  rw [embed_restricted emitReg emitStack emitReg_injective emitStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 0) (d.stacks 7)
    (if selected then true :: (Encoding.frame bits ++ d.stacks 2) else d.stacks 2) []
  let e := embedState emitReg emitStack d b
  have hstack (i : Fin 4) : e.stacks (emitStack i) = b.stacks i :=
    embedState_stack _ _ _ _ emitStack_injective i
  have hreg (i : Fin 3) : e.regs (emitReg i) = b.regs i :=
    embedState_register _ _ _ _ emitReg_injective i
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [emitStack, b, SubexpNormalizeProgram.filterState] using hstack 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 0
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 1
  · simpa [emitReg, b, SubexpNormalizeProgram.filterState] using hreg 2

abbrev selectMissing : Cmd 10 8 := .base (.atom (.bnot 9 4))
def selectedState (d : Data) : Data := ⟨Function.update d.regs 9 (!(d.regs 4)), d.stacks⟩

theorem selectMissing_eval (d : Data) : Eval selectMissing 1 d (selectedState d) := by
  apply Eval.base
  simpa [selectedState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
    StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 4) d

abbrev callback : Cmd 10 8 :=
  .seq copySuffix (.seq ExecCNFSubset.memberCall (.seq selectMissing
    (.seq (ExecCNFSubset.clear 3) (.seq (ExecCNFSubset.clear 4) emitCall))))

def callbackBound (bits : List Bool) (rest : List (List Bool)) : ℕ :=
  (20 * bits.length + 39) * (Encoding.encodeList id rest).length + 5 * bits.length + 28

theorem callback_eval (bits : List Bool) (rest : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id rest)
    (hquery : d.stacks 1 = bits.reverse) (hclean : Clean d) :
    ∃ n ≤ callbackBound bits rest, ∃ e : Data, Eval callback n d e ∧ Clean e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = (if bits ∈ rest then d.stacks 2
        else true :: (Encoding.frame bits ++ d.stacks 2)) ∧
      e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  rcases hclean with ⟨h3, h4, h5, h6, h7⟩
  obtain ⟨m, hm, e, he, hanswer, hresidual, houtput, hquery', hcopy, htmp,
      hsource', hacc, hscratch, htag, hpresent, hfound⟩ :=
    ExecCNFSubset.memberCall_eval bits rest (copied d)
      (by simp [copied, StackRoutines.copyStacks, hsource, h3])
      (by simpa [copied, StackRoutines.copyStacks] using hquery)
      (by simpa [copied, StackRoutines.copyStacks] using h4)
      (by simpa [copied, StackRoutines.copyStacks] using h5)
      (by simpa [copied, StackRoutines.copyStacks] using h6)
  let c₁ := ExecCNFSubset.cleared 3 (selectedState e)
  let c₂ := ExecCNFSubset.cleared 4 c₁
  have cq : c₂.stacks 1 = bits.reverse := by
    simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks] using hquery'
  have cs : c₂.regs 9 = !(decide (bits ∈ rest)) := by
    simp [c₂, c₁, selectedState, readRegs, hanswer]
  obtain ⟨f, hf, fs, fp, fo, f3, f4, f5, f6, f7, ft, fpr, ff⟩ :=
    emitCall_eval (!(decide (bits ∈ rest))) bits c₂ cq cs
  let steps := (7 * (d.stacks 0).length + 5) +
    (m + (1 + ((2 * (e.stacks 3).length + 3) +
      ((2 * (c₁.stacks 4).length + 3) +
        (SubexpNormalizeProgram.emitIfSelectedSteps (!(decide (bits ∈ rest))) bits + 1)))))
  have hlen4 : (c₁.stacks 4).length = 1 := by
    simp [c₁, selectedState, StackRoutines.clearStacks, houtput]
  have hemit := SubexpNormalizeProgram.emitIfSelected_steps_le (!(decide (bits ∈ rest))) bits
  refine ⟨steps, ?_, f, ?_, ?_, ?_, fp, ?_, ft, fpr, ff⟩
  · dsimp [steps, callbackBound]
    rw [hsource, hlen4]
    nlinarith
  · exact Eval.seq (copySuffix_eval d h7) (Eval.seq he (Eval.seq (selectMissing_eval e)
      (Eval.seq (ExecCNFSubset.clear_eval 3 (selectedState e))
        (Eval.seq (ExecCNFSubset.clear_eval 4 c₁) hf))))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [c₂, c₁, ExecCNFSubset.cleared, StackRoutines.clearStacks] using f3
    · simpa [c₂, ExecCNFSubset.cleared, StackRoutines.clearStacks] using f4
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks, hcopy] using f5
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks, htmp] using f6
    · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
        hscratch, copied, StackRoutines.copyStacks, h7] using f7
  · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
      hsource', copied, StackRoutines.copyStacks] using fs
  · simpa [c₂, c₁, ExecCNFSubset.cleared, selectedState, StackRoutines.clearStacks,
      hacc, copied, StackRoutines.copyStacks] using fo

@[simp] theorem clean_state (base : Data) (v pr f : Bool) (src payload : List Bool) :
    Clean (RecordPrograms.state ports base v pr f src payload) ↔ Clean base := by
  simp [Clean, RecordPrograms.state ]

@[simp] theorem state_output (base : Data) (v pr f : Bool) (src payload : List Bool) :
    (RecordPrograms.state ports base v pr f src payload).stacks 2 = base.stacks 2 := by
  simp [RecordPrograms.state ]

theorem callback_state_eval (bits : List Bool) (rest : List (List Bool))
    (base : Data) (valid : Clean base) :
    ∃ (n : ℕ) (next : Data), n ≤ callbackBound bits rest ∧ Clean next ∧
      next.stacks 2 = (if bits ∈ rest then base.stacks 2
        else true :: (Encoding.frame bits ++ base.stacks 2)) ∧
      Eval callback n
        (RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse)
        (RecordPrograms.state ports next false true false (Encoding.encodeList id rest) []) := by
  let d := RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse
  obtain ⟨n, hn, next, he, hclean, hs, hp, ho, ht, hpr, hf⟩ :=
    callback_eval bits rest d (by simp [d, RecordPrograms.state ])
      (by simp [d, RecordPrograms.state ])
      ((clean_state _ _ _ _ _ _).mpr valid)
  have hs' : next.stacks 0 = Encoding.encodeList id rest := by
    simpa [d, RecordPrograms.state, ports] using hs
  have hend : RecordPrograms.state ports next false true false (Encoding.encodeList id rest) [] = next :=
    RecordPrograms.state_eq_self ports next false true false _ [] ht hpr hf hs' hp
  refine ⟨n, next, hn, hclean, ?_, ?_⟩
  · simpa [d] using ho
  · rw [hend]
    exact he

/-- The suffix-dependent cost counts the actual complete callback at each
record; the parser and loop-control costs are included separately. -/
def budget : List (List Bool) → ℕ
  | [] => 0
  | bits :: rest => 6 * bits.length + callbackBound bits rest + 7 + budget rest

theorem loop_run (records acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) :
    ∃ (n : ℕ) (next : Data), n ≤ 1 + budget records ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id ((ExecCNF.dedupLiterals records).reverse ++ acc) ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports base records [])
        (RecordPrograms.state ports next false true false [] []) := by
  induction records generalizing base acc with
  | nil =>
      refine ⟨1, base, by simp [budget], valid, ?_, ?_⟩
      · simpa [ExecCNF.dedupLiterals] using hacc
      · apply Eval.while_false
        change false = false
        rfl
  | cons bits rest ih =>
      obtain ⟨n, middle, hn, hmiddle, hout, hc⟩ := callback_state_eval bits rest base valid
      let acc' := if bits ∈ rest then acc else bits :: acc
      have hacc' : middle.stacks 2 = Encoding.encodeList id acc' := by
        by_cases hm : bits ∈ rest
        · simpa [acc', hm, hacc] using hout
        · simpa [acc', hm, hacc, Encoding.encodeList] using hout
      obtain ⟨m, next, hm, hnext, hresult, hrest⟩ := ih acc' middle hmiddle hacc'
      have hreader : Eval (RecordPrograms.reader ports) (6 * bits.length + 4)
          (RecordPrograms.afterTag ports base (bits :: rest) [])
          (RecordPrograms.state ports base false true false (Encoding.encodeList id rest) bits.reverse) := by
        simpa [RecordPrograms.afterTag] using
          RecordPrograms.reader_eval ports base bits (Encoding.encodeList id rest) [] true true false
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports middle false true false (Encoding.encodeList id rest) [])
          (RecordPrograms.afterTag ports middle rest []) := by
        apply Eval.ite_false (by change false = false; rfl)
        simpa using RecordPrograms.pop_list_eval ports middle rest [] false true
      have hbody := Eval.seq hreader (Eval.seq hc hbranch)
      have hrun := Eval.while_true (body := RecordPrograms.body ports callback)
        (by change true = true; rfl) hbody hrest
      refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, hnext, ?_, hrun⟩
      · simp only [budget]
        omega
      · by_cases hmem : bits ∈ rest
        · have hc' := (ExecCNF.contains_true bits rest).mpr hmem
          simpa [ExecCNF.dedupLiterals, hc', acc', hmem] using hresult
        · have hc' : ExecCNF.contains bits rest ≠ true := by
            intro h
            exact hmem ((ExecCNF.contains_true bits rest).mp h)
          simpa [ExecCNF.dedupLiterals, hc', acc', hmem, List.reverse_cons,
            List.append_assoc] using hresult

abbrev scan : Cmd 10 8 := RecordPrograms.iterate ports callback

theorem scan_eval (records acc : List (List Bool)) (base : Data)
    (valid : Clean base) (hacc : base.stacks 2 = Encoding.encodeList id acc) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 3 + budget records ∧ Clean next ∧
      next.stacks 2 = Encoding.encodeList id ((ExecCNF.dedupLiterals records).reverse ++ acc) ∧
      Eval scan n (RecordPrograms.state ports base v pr f (Encoding.encodeList id records) [])
        (RecordPrograms.state ports next false true false [] []) := by
  obtain ⟨n, next, hn, hnext, hout, hloop⟩ := loop_run records acc base valid hacc
  refine ⟨1 + (1 + n), next, by omega, hnext, hout, ?_⟩
  apply Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
  apply Eval.seq _ hloop
  simpa using RecordPrograms.pop_list_eval ports base records [] v pr

theorem budget_le (records : List (List Bool)) :
    budget records ≤ 100 * (Encoding.encodeList id records).length ^ 2 := by
  induction records with
  | nil => simp [budget]
  | cons bits rest ih =>
      simp only [budget, callbackBound, Encoding.length_encodeList_cons, id_eq]
      nlinarith [Nat.zero_le (bits.length * bits.length),
        Nat.zero_le (bits.length * (Encoding.encodeList id rest).length)]

theorem encoded_dedup_length_le (records : List (List Bool)) :
    (Encoding.encodeList id (ExecCNF.dedupLiterals records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
      unfold ExecCNF.dedupLiterals
      split
      · simp only [Encoding.length_encodeList_cons, id_eq]
        omega
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left ih (2 * bits.length + 2)

def reverseStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 2 else if i = 1 then 7 else if i = 2 then 0 else 1

theorem reverseStack_injective : Function.Injective reverseStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [reverseStack]

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitReg reverseStack
abbrev reverseCall : Cmd 10 8 := .call reverseProgram

theorem reverseCall_eval (records acc : List (List Bool)) (d : Data)
    (hsource : d.stacks 2 = Encoding.encodeList id records)
    (houtput : d.stacks 0 = Encoding.encodeList id acc) (hpayload : d.stacks 1 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval reverseCall n d e ∧
      e.stacks 0 = Encoding.encodeList id (records.reverse ++ acc) ∧
      e.stacks 1 = [] ∧ e.stacks 2 = [] ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = d.stacks 5 ∧ e.stacks 6 = d.stacks 6 ∧ e.stacks 7 = d.stacks 7 := by
  let a : State 3 4 := ⟨d.regs ∘ emitReg, d.stacks ∘ reverseStack⟩
  have ha : a = SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id records) (d.stacks 7) (Encoding.encodeList id acc) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ emitReg ]
    · funext i
      fin_cases i <;> simp [ reverseStack,
        hsource, houtput, hpayload]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks 7) (d.regs 7) (d.regs 8) (d.regs 9)
  simp only [List.append_nil] at ht
  rw [← ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    emitReg reverseStack d emitReg_injective reverseStack_injective ht
  rw [embed_restricted emitReg reverseStack emitReg_injective reverseStack_injective d] at he
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 7)
    (Encoding.encodeList id (records.reverse ++ acc)) []
  let e := embedState emitReg reverseStack d b
  have hstack (i : Fin 4) : e.stacks (reverseStack i) = b.stacks i :=
    embedState_stack _ _ _ _ reverseStack_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 2
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 3
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 0
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · simpa [reverseStack, b, SubexpNormalizeProgram.filterState] using hstack 1

abbrev pushFalse (stack : Fin 8) : Cmd 10 8 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 8) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 8) (d : Data) : Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 10) (s := 8) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 10) (s := 8) stack 0) middle
  exact Eval.seq h₁ h₂

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

/-- The complete routine uses its input stack again for the final ordered
output. Its reversed accumulator and every work stack finish empty. -/
abbrev dedup : Cmd 10 8 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

def Ready (d : Data) : Prop := Clean d ∧ d.stacks 1 = [] ∧ d.stacks 2 = []

theorem dedup_eval (records : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id records) (hready : Ready d) :
    ∃ n ≤ 100 * (Encoding.encodeList id records).length ^ 2 +
        10 * (Encoding.encodeList id records).length + 7,
      ∃ e : Data, Eval dedup n d e ∧ Ready e ∧
        e.stacks 0 = Encoding.encodeList id (ExecCNF.dedupLiterals records) := by
  rcases hready with ⟨hclean, hpayload, houtput⟩
  let a := pushed 2 d
  have ha : Clean a := by simpa [a, pushed, Clean] using hclean
  have hao : a.stacks 2 = Encoding.encodeList id [] := by simp [a, pushed, houtput, Encoding.encodeList]
  obtain ⟨n, next, hn, hnext, hout, hs⟩ := scan_eval records [] a ha hao
    (a.regs 7) (a.regs 8) (a.regs 9)
  have hstart : RecordPrograms.state ports a (a.regs 7) (a.regs 8) (a.regs 9)
      (Encoding.encodeList id records) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, pushed] using hsource
    · simpa [a, pushed] using hpayload
  rw [hstart] at hs
  let b := RecordPrograms.state ports next false true false [] []
  let c := pushed 0 b
  have hc : Clean c := by simpa [c, pushed, b, Clean, RecordPrograms.state, ports] using hnext
  have hc2 : c.stacks 2 = Encoding.encodeList id (ExecCNF.dedupLiterals records).reverse := by
    simpa [c, pushed, b] using hout
  have hc0 : c.stacks 0 = Encoding.encodeList id [] := by
    simp [c, pushed, b, RecordPrograms.state, Encoding.encodeList]
  have hc1 : c.stacks 1 = [] := by simp [c, pushed, b, RecordPrograms.state ]
  obtain ⟨m, hm, e, he, he0, he1, he2, he3, he4, he5, he6, he7⟩ :=
    reverseCall_eval (ExecCNF.dedupLiterals records).reverse [] c hc2 hc0 hc1
  have hcost := budget_le records
  have hlength := encoded_dedup_length_le records
  rw [encoded_reverse_length] at hm
  refine ⟨2 + (n + (2 + m)), ?_, e, ?_, ?_, ?_⟩
  · omega
  · exact Eval.seq (pushFalse_eval 2 d) (Eval.seq hs (Eval.seq (pushFalse_eval 0 b) he))
  · refine ⟨?_, he1, he2⟩
    rcases hc with ⟨hc3, hc4, hc5, hc6, hc7⟩
    exact ⟨he3.trans hc3, he4.trans hc4, he5.trans hc5, he6.trans hc6, he7.trans hc7⟩
  · simpa using he0

def dedupProgram := compiled dedup 0 0

theorem dedup_runsIn (records : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id records) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = Encoding.encodeList id (ExecCNF.dedupLiterals records) ∧
      RunsIn dedupProgram (120 * ((Encoding.encodeList id records).length + 1) ^ 2)
        (d.withPC (some dedupProgram.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := dedup_eval records d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  nlinarith

theorem dedup_primitive_execution (records : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id records) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = Encoding.encodeList id (ExecCNF.dedupLiterals records) ∧
      Computation.RunsIn (primitive dedupProgram).step
        (primitiveOverhead dedupProgram * (120 * ((Encoding.encodeList id records).length + 1) ^ 2))
        (primitiveCfg dedupProgram (d.withPC (some dedupProgram.entry)))
        (primitiveCfg dedupProgram (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := dedup_runsIn records d hsource hready
  exact ⟨e, he, hout, primitive_execution dedupProgram hrun⟩

theorem dedup_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    ExecCNF.dedupLiterals (xs.map f) = (ExecCNF.dedupLiterals xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hm : ExecCNF.contains (f x) (xs.map f) = true ↔
          ExecCNF.contains x xs = true := by
        rw [ExecCNF.contains_true, ExecCNF.contains_true, List.mem_map]
        constructor
        · rintro ⟨y, hy, h⟩
          exact hf h ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      by_cases h : ExecCNF.contains x xs = true
      · have h' := hm.mpr h
        simp [ExecCNF.dedupLiterals, h, h', ih]
      · have h' : ExecCNF.contains (f x) (xs.map f) ≠ true := fun hx => h (hm.mp hx)
        simp [ExecCNF.dedupLiterals, h, h', ih]

theorem encode_nat_records (xs : List ℕ) :
    Encoding.encodeList id (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

/-- On actual unary literal fields, the result is precisely the executable
CNF normalizer's stable, last-occurrence literal deduplication. -/
theorem literal_runsIn (clause : List ℕ) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList Encoding.encodeNat clause) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals clause) ∧
      RunsIn dedupProgram
        (120 * ((Encoding.encodeList Encoding.encodeNat clause).length + 1) ^ 2)
        (d.withPC (some dedupProgram.entry)) (e.withPC none) := by
  have hs : d.stacks 0 = Encoding.encodeList id (clause.map Encoding.encodeNat) := by
    simpa only [encode_nat_records] using hsource
  obtain ⟨e, he, hout, hr⟩ := dedup_runsIn (clause.map Encoding.encodeNat) d hs hready
  rw [dedup_map Encoding.encodeNat Encoding.encodeNat_injective, encode_nat_records] at hout
  exact ⟨e, he, hout, by simpa only [encode_nat_records] using hr⟩

theorem literal_primitive_execution (clause : List ℕ) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList Encoding.encodeNat clause) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 0 = Encoding.encodeList Encoding.encodeNat (ExecCNF.dedupLiterals clause) ∧
      Computation.RunsIn (primitive dedupProgram).step
        (primitiveOverhead dedupProgram *
          (120 * ((Encoding.encodeList Encoding.encodeNat clause).length + 1) ^ 2))
        (primitiveCfg dedupProgram (d.withPC (some dedupProgram.entry)))
        (primitiveCfg dedupProgram (e.withPC none)) := by
  obtain ⟨e, he, hout, hr⟩ := literal_runsIn clause d hsource hready
  exact ⟨e, he, hout, primitive_execution dedupProgram hr⟩

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
