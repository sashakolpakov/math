import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNegatedQueryProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFSubset
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram

namespace OAI.Algorithms

/-!
# Actual encoded-clause tautology testing

The outer iterator reads unary literal records. For each literal, a concrete
program builds its opposite's query, copies the preserved clause, and runs the
proved encoded membership program. All data-dependent repetition is in those
finite programs and the record iterator.
-/

namespace SubexponentialSAT.SubexpTautologyProgram

open BitProgram StructuredCalls

abbrev Data := State 10 8

def negateReg (i : Fin 2) : Fin 10 := Fin.castAdd 8 i

def negateStack (i : Fin 4) : Fin 8 :=
  match i.val with
  | 0 => 7
  | 1 => 1
  | 2 => 5
  | _ => 6

theorem negateReg_injective : Function.Injective negateReg := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 10 => i.val) h)

theorem negateStack_injective : Function.Injective negateStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [negateStack]

def negateQueryProgram := ProgramLinking.liftProgram
  SubexpNegatedQueryProgram.program negateReg negateStack

abbrev negateQuery : Cmd 10 8 := .call negateQueryProgram

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

theorem negateQuery_eval (c : ℕ) (d : Data)
    (hq : d.stacks 7 = (Encoding.encodeNat c).reverse)
    (h1 : d.stacks 1 = []) (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) :
    ∃ e : Data,
      Eval negateQuery (SubexpNegatedQueryProgram.steps c) d e ∧
      e.stacks 1 = (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = d.stacks 3 ∧ e.stacks 4 = d.stacks 4 ∧
      e.stacks 5 = [] ∧ e.stacks 6 = [] ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  let a := SubexpNegatedQueryProgram.state (d.regs 0) (d.regs 1)
    (Encoding.encodeNat c).reverse [] [] []
  let b := SubexpNegatedQueryProgram.state false false (Encoding.encodeNat c).reverse
    (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse [] []
  have ha : a = ⟨d.regs ∘ negateReg, d.stacks ∘ negateStack⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [
        SubexpNegatedQueryProgram.slots, negateStack, hq, h1, h5, h6]
  let e := embedState negateReg negateStack d b
  have he := eval_call_lifted SubexpNegatedQueryProgram.program negateReg negateStack d
    negateReg_injective negateStack_injective
    (SubexpNegatedQueryProgram.program_trace c (d.regs 0) (d.regs 1))
  change Eval negateQuery (SubexpNegatedQueryProgram.steps c)
    (embedState negateReg negateStack d a) e at he
  rw [ha, embed_restricted _ _ negateReg_injective negateStack_injective] at he
  refine ⟨e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack negateReg negateStack d b negateStack_injective 1
  · exact embedState_stack_frame negateReg negateStack d b 0 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 2 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 3 (by decide)
  · exact embedState_stack_frame negateReg negateStack d b 4 (by decide)
  · exact embedState_stack negateReg negateStack d b negateStack_injective 2
  · exact embedState_stack negateReg negateStack d b negateStack_injective 3
  · exact (embedState_stack negateReg negateStack d b negateStack_injective 0).trans hq.symm
  · exact embedState_register_frame negateReg negateStack d b 7 (by decide)
  · exact embedState_register_frame negateReg negateStack d b 8 (by decide)
  · exact embedState_register_frame negateReg negateStack d b 9 (by decide)

/-- The current literal uses stack 7, so stack 4 is the copying scratch port. -/
abbrev copyClauseProgram : Program 10 8 8 := StackRoutines.copyProgram 2 3 4 0 1

abbrev copyClause : Cmd 10 8 := .call copyClauseProgram

theorem copyClause_eval (d : Data) (h4 : d.stacks 4 = []) :
    Eval copyClause (7 * (d.stacks 2).length + 5) d (ExecCNFSubset.copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8) 2 3 4 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h4
  have hh := StackRoutines.halt_after_trace copyClauseProgram h 7 rfl rfl
  apply Eval.call
  simpa [copyClauseProgram, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, ExecCNFSubset.copied, StructuredProgram.State.withPC, Nat.add_assoc] using hh

def encodedClause (C : List ℕ) : List Bool := Encoding.encodeList Encoding.encodeNat C

def literalRecords (C : List ℕ) : List (List Bool) := C.map Encoding.encodeNat

theorem encodedClause_records (C : List ℕ) :
    encodedClause C = Encoding.encodeList id (literalRecords C) := by
  induction C with
  | nil => rfl
  | cons c C ih => simpa [encodedClause, literalRecords, Encoding.encodeList] using ih

def oppositePresent (C : List ℕ) (bits : List Bool) : Bool :=
  match Encoding.readNat bits with
  | none => false
  | some (c, rest) => rest.isEmpty && ExecCNF.contains (SubexpFrontend.negateCode c) C

@[simp] theorem oppositePresent_encodeNat (C : List ℕ) (c : ℕ) :
    oppositePresent C (Encoding.encodeNat c) =
      ExecCNF.contains (SubexpFrontend.negateCode c) C := by
  simp [oppositePresent]

theorem member_opposite (C : List ℕ) (c : ℕ) :
    decide (Encoding.encodeNat (SubexpFrontend.negateCode c) ∈ literalRecords C) =
      ExecCNF.contains (SubexpFrontend.negateCode c) C := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, literalRecords, List.mem_map, ExecCNF.contains_true]
  constructor
  · rintro ⟨x, hx, he⟩
    exact Encoding.encodeNat_injective he ▸ hx
  · intro h
    exact ⟨_, h, rfl⟩

theorem any_oppositePresent (C : List ℕ) :
    (literalRecords C).any (oppositePresent C) =
      ExecCNF.tautology SubexpFrontend.negateCode C := by
  simp [literalRecords, List.any_map, ExecCNF.tautology, Function.comp_def]

def mark (d : Data) : Data :=
  ⟨Function.update d.regs 9 (d.regs 4), d.stacks⟩

theorem mark_eval (d : Data) :
    Eval (RecordPrograms.atom (.copy 9 4)) 1 d (mark d) := by
  have h : (StructuredProgram.Atom.copy (r := 10) (s := 8) 9 4).eval d = mark d := rfl
  rw [← h]
  exact .base (.atom _ _)

abbrev callback : Cmd 10 8 :=
  .seq negateQuery (.seq copyClause (.seq ExecCNFSubset.memberCall
    (.seq (RecordPrograms.atom (.copy 9 4))
      (.seq (ExecCNFSubset.clear 1) (.seq (ExecCNFSubset.clear 3)
        (.seq (ExecCNFSubset.clear 4) (ExecCNFSubset.clear 7)))))))

def invariant (C : List ℕ) (d : Data) : Prop :=
  d.stacks 2 = encodedClause C ∧ d.stacks 1 = [] ∧ d.stacks 3 = [] ∧
    d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = []

def perLiteralCost (C : List ℕ) (bits : List Bool) : ℕ :=
  100 * ((encodedClause C).length + 1) * (bits.length + 1)

theorem callback_eval (C : List ℕ) (c : ℕ) (d : Data)
    (hquery : d.stacks 7 = (Encoding.encodeNat c).reverse) (valid : invariant C d) :
    ∃ n ≤ perLiteralCost C (Encoding.encodeNat c), ∃ e : Data,
      Eval callback n d e ∧ invariant C e ∧
      e.regs 9 = ExecCNF.contains (SubexpFrontend.negateCode c) C ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 7 = [] ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 := by
  rcases valid with ⟨hd2, hd1, hd3, hd4, hd5, hd6⟩
  obtain ⟨a, hneg, ha1, ha0, ha2, ha3, ha4, ha5, ha6, ha7, har7, har8, har9⟩ :=
    negateQuery_eval c d hquery hd1 hd5 hd6
  have hsrc : (ExecCNFSubset.copied a).stacks 3 =
      Encoding.encodeList id (literalRecords C) := by
    simp [ StackRoutines.copyStacks, ha2, hd2, ha3, hd3,
      encodedClause_records]
  have hq : (ExecCNFSubset.copied a).stacks 1 =
      (Encoding.encodeNat (SubexpFrontend.negateCode c)).reverse := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha1
  have ho : (ExecCNFSubset.copied a).stacks 4 = [] := by
    simp [ StackRoutines.copyStacks, ha4, hd4]
  have hc : (ExecCNFSubset.copied a).stacks 5 = [] := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha5
  have ht : (ExecCNFSubset.copied a).stacks 6 = [] := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks] using ha6
  obtain ⟨m, hm, b, hmem, hbans, hbres, hb4, hb1, hb5, hb6,
      hb0, hb2, hb7, hbr7, hbr8, hbr9⟩ :=
    ExecCNFSubset.memberCall_eval (Encoding.encodeNat (SubexpFrontend.negateCode c))
      (literalRecords C) (ExecCNFSubset.copied a) hsrc hq ho hc ht
  let result := ExecCNFSubset.cleared 7 (ExecCNFSubset.cleared 4
    (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
  let steps := SubexpNegatedQueryProgram.steps c +
    ((7 * (a.stacks 2).length + 5) +
    (m + (1 + ((2 * (b.stacks 1).length + 3) +
      ((2 * (b.stacks 3).length + 3) +
      ((2 * (b.stacks 4).length + 3) + (2 * (b.stacks 7).length + 3)))))))
  have hb7' : b.stacks 7 = (Encoding.encodeNat c).reverse := by
    simpa [ExecCNFSubset.copied, StackRoutines.copyStacks, ha7, hquery] using hb7
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn := SubexpNegatedQueryProgram.steps_le c
    have hlen : (Encoding.encodeNat (SubexpFrontend.negateCode c)).length ≤
        (Encoding.encodeNat c).length + 1 := by
      simpa only [Encoding.length_encodeNat] using
        Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
    rw [← encodedClause_records] at hm hbres
    dsimp [steps, perLiteralCost]
    rw [ha2, hd2, hb1, hb4, hb7']
    simp only [List.length_reverse, List.length_cons, List.length_nil]
    nlinarith
  · apply Eval.seq hneg
    apply Eval.seq (copyClause_eval a (ha4.trans hd4))
    apply Eval.seq hmem
    apply Eval.seq (mark_eval b)
    apply Eval.seq (ExecCNFSubset.clear_eval 1 (mark b))
    apply Eval.seq (ExecCNFSubset.clear_eval 3 (ExecCNFSubset.cleared 1 (mark b)))
    apply Eval.seq (ExecCNFSubset.clear_eval 4
      (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
    simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using
      ExecCNFSubset.clear_eval 7 (ExecCNFSubset.cleared 4
        (ExecCNFSubset.cleared 3 (ExecCNFSubset.cleared 1 (mark b))))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark,
        ExecCNFSubset.copied, StackRoutines.copyStacks, ha2, hd2] using hb2
    · simp [result, StackRoutines.clearStacks, mark]
    · simp [result, StackRoutines.clearStacks, mark]
    · simp [result, StackRoutines.clearStacks, mark]
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using hb5
    · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark] using hb6
  · simp [result, readRegs, mark, hbans, member_opposite]
  · simpa [result, ExecCNFSubset.cleared, StackRoutines.clearStacks, mark,
      ExecCNFSubset.copied, StackRoutines.copyStacks, ha0] using hb0
  · simp [result, StackRoutines.clearStacks]
  · simpa [result, ExecCNFSubset.cleared, readRegs, mark,
      ExecCNFSubset.copied, har7] using hbr7
  · simpa [result, ExecCNFSubset.cleared, readRegs, mark,
      ExecCNFSubset.copied, har8] using hbr8

def ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 7
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def UnaryPayload (bits : List Bool) : Prop := ∃ c, bits = Encoding.encodeNat c

theorem callback_contract (C : List ℕ) :
    RecordPrograms.CallbackContractOn ports callback (oppositePresent C)
      (perLiteralCost C) (invariant C) UnaryPayload := by
  intro bits tail base hbits hbase
  obtain ⟨c, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Encoding.encodeNat c).reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd7 : d.stacks 7 = (Encoding.encodeNat c).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hr7 : d.regs 7 = false := by simp [d, RecordPrograms.state, ports]
  have hr8 : d.regs 8 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant C d := by
    simpa [invariant, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, hv, ha, hs, hp, h7, h8⟩ := callback_eval C c d hd7 hv
  have heState : RecordPrograms.state ports e false true
      (oppositePresent C (Encoding.encodeNat c)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h7.trans hr7) (h8.trans hr8)
      (by simpa [ports] using ha) (hs.trans hd0) hp
  refine ⟨n, e, hn, hv, ?_⟩
  rw [heState]
  exact he

theorem valid_literalRecords (C : List ℕ) :
    ∀ bits ∈ literalRecords C, UnaryPayload bits := by
  intro bits h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
  exact ⟨c, rfl⟩

theorem budget_le (C : List ℕ) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perLiteralCost C) records ≤
      110 * ((encodedClause C).length + 1) * (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]; omega
  | cons bits records ih =>
    have hstep : 6 * bits.length + perLiteralCost C bits + 7 ≤
        110 * ((encodedClause C).length + 1) * (2 * bits.length + 2) := by
      unfold perLiteralCost
      nlinarith
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perLiteralCost C bits + 7 +
          RecordPrograms.budget (perLiteralCost C) records)
          = (6 * bits.length + perLiteralCost C bits + 7) +
            (3 + RecordPrograms.budget (perLiteralCost C) records) := by omega
      _ ≤ 110 * ((encodedClause C).length + 1) * (2 * bits.length + 2) +
          110 * ((encodedClause C).length + 1) * (Encoding.encodeList id records).length :=
        Nat.add_le_add hstep ih
      _ = 110 * ((encodedClause C).length + 1) *
          (2 * bits.length + 2 + (Encoding.encodeList id records).length) := by ring

/-- Copy the input clause once, before the destructive outer scan. -/
abbrev initializeProgram : Program 10 8 8 := StackRoutines.copyProgram 0 2 4 0 1

def initialized (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 0 2 d.stacks⟩

abbrev initializeCmd : Cmd 10 8 := .call initializeProgram

theorem initialize_eval (d : Data) (h4 : d.stacks 4 = []) :
    Eval initializeCmd (7 * (d.stacks 0).length + 5) d (initialized d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8) 0 2 4 0 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h4
  have hh := StackRoutines.halt_after_trace initializeProgram h 7 rfl rfl
  apply Eval.call
  simpa [initializeProgram, StackRoutines.copyResult, StackRoutines.copyStacks,
    readRegs, initialized, StructuredProgram.State.withPC, Nat.add_assoc] using hh

def Ready (d : Data) : Prop := ∀ i : Fin 8, i ≠ 0 → d.stacks i = []

def finished (d : Data) : Data :=
  ⟨(ExecCNFSubset.cleared 0 d).regs,
    Function.update (ExecCNFSubset.cleared 0 d).stacks 1 [d.regs 9]⟩

abbrev finish : Cmd 10 8 :=
  .seq (ExecCNFSubset.clear 0) (RecordPrograms.atom (.push 1 9))

theorem finish_eval (d : Data) (h1 : d.stacks 1 = []) :
    Eval finish (2 * (d.stacks 0).length + 4) d (finished d) := by
  have hpush : Eval (RecordPrograms.atom (.push 1 9)) 1
      (ExecCNFSubset.cleared 0 d) (finished d) := by
    have h : (StructuredProgram.Atom.push (r := 10) (s := 8) 1 9).eval
        (ExecCNFSubset.cleared 0 d) = finished d := by
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
        finished, StackRoutines.clearStacks, readRegs, h1]
    rw [← h]
    exact .base (.atom _ _)
  simpa [finish, Nat.add_assoc] using (ExecCNFSubset.clear_eval 0 d).seq hpush

abbrev tautology : Cmd 10 8 :=
  .seq initializeCmd (.seq (RecordPrograms.iterate ports callback) finish)

/-- Complete clause testing, including its actual initialization and cleanup.
The clause remains on stack 2, and stack 1 contains the Boolean answer. -/
theorem tautology_eval (C : List ℕ) (d : Data)
    (hsource : d.stacks 0 = encodedClause C) (hready : Ready d) :
    ∃ n ≤ 199 * ((encodedClause C).length + 1) ^ 2, ∃ e : Data,
      Eval tautology n d e ∧
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 1 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 2 = encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks i = []) := by
  let a := initialized d
  have hinit := initialize_eval d (hready 4 (by decide))
  have ha0 : a.stacks 0 = encodedClause C := by
    simpa [a, initialized, StackRoutines.copyStacks] using hsource
  have ha7 : a.stacks 7 = [] := by
    simpa [a, initialized, StackRoutines.copyStacks] using hready 7 (by decide)
  have ha : invariant C a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [a, initialized, StackRoutines.copyStacks, hsource,
        hready 1 (by decide), hready 2 (by decide), hready 3 (by decide),
        hready 4 (by decide), hready 5 (by decide), hready 6 (by decide)]
  have haState : RecordPrograms.state ports a (a.regs 7) (a.regs 8) (a.regs 9)
      (Encoding.encodeList id (literalRecords C) ++ []) [] = a :=
    RecordPrograms.state_eq_self ports a _ _ _ _ _ rfl rfl rfl
      (by simpa [ports, ← encodedClause_records] using ha0) ha7
  obtain ⟨m, b, hm, hb, hloop⟩ := RecordPrograms.iterate_run_on ports callback
    (oppositePresent C) (perLiteralCost C) (invariant C) UnaryPayload
    (callback_contract C) (literalRecords C) [] a (valid_literalRecords C) ha
    (a.regs 7) (a.regs 8) (a.regs 9)
  rw [haState, any_oppositePresent] at hloop
  let middle := RecordPrograms.state ports b false true
    (ExecCNF.tautology SubexpFrontend.negateCode C)
    (RecordPrograms.unread (oppositePresent C) (literalRecords C) []) []
  have hm1 : middle.stacks 1 = [] := by
    simpa [middle, RecordPrograms.state, ports] using hb.2.1
  have hfinish := finish_eval middle hm1
  let n := (7 * (d.stacks 0).length + 5) + (m + (2 * (middle.stacks 0).length + 4))
  refine ⟨n, ?_, finished middle, ?_, ?_, ?_, ?_, ?_⟩
  · have hbudget := budget_le C (literalRecords C)
    rw [← encodedClause_records] at hbudget
    have hres := ExecCNFSubset.unread_length_le (oppositePresent C) (literalRecords C)
    rw [← encodedClause_records] at hres
    have hm0 : middle.stacks 0 =
        RecordPrograms.unread (oppositePresent C) (literalRecords C) [] := by
      simp [middle, RecordPrograms.state, ports]
    dsimp [n]
    rw [hsource, hm0]
    nlinarith
  · exact hinit.seq (hloop.seq hfinish)
  · simp [finished, middle, readRegs, RecordPrograms.state, ports]
  · simp [finished, middle, RecordPrograms.state, ports]
  · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
      RecordPrograms.state, ports] using hb.1
  · intro i hi1 hi2
    fin_cases i
    · simp [finished, StackRoutines.clearStacks]
    · exact (hi1 rfl).elim
    · exact (hi2 rfl).elim
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.2.1
    · simpa [finished, middle, ExecCNFSubset.cleared, StackRoutines.clearStacks,
        RecordPrograms.state, ports] using hb.2.2.2.2.2
    · simp [finished, middle, StackRoutines.clearStacks,
        RecordPrograms.state, ports]

def program := compiled tautology 0 1

theorem tautology_runsIn (C : List ℕ) (d : Data)
    (hsource : d.stacks 0 = encodedClause C) (hready : Ready d) :
    ∃ e : Data,
      e.regs 9 = ExecCNF.tautology SubexpFrontend.negateCode C ∧
      e.stacks 1 = [ExecCNF.tautology SubexpFrontend.negateCode C] ∧
      e.stacks 2 = encodedClause C ∧
      (∀ i : Fin 8, i ≠ 1 → i ≠ 2 → e.stacks i = []) ∧
      RunsIn program (200 * ((encodedClause C).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, ho, hc, hw⟩ := tautology_eval C d hsource hready
  refine ⟨e, hr, ho, hc, hw, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hpos : 0 < ((encodedClause C).length + 1) ^ 2 := pow_pos (by omega) _
  omega

end SubexponentialSAT.SubexpTautologyProgram

end OAI.Algorithms
