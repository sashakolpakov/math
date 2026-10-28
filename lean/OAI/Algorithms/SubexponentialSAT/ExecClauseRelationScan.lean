import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationsProgram
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-!
# Actual clause-relation scans over encoded formulas

All modes use a fixed finite Boolean program. An outer record iterator parses
each encoded clause, then invokes the concrete preserving clause-relation
program. The query clause is preserved for callers that subsequently emit it.
-/
namespace SubexponentialSAT.ExecClauseRelationScan
open BitProgram StructuredCalls

abbrev Clause := List (List Bool)
abbrev Formula := List Clause
abbrev Data := State 15 12

def encodeClause (C : Clause) : List Bool := Encoding.encodeList id C

inductive Mode
  | equivalent
  | strictSubset
  | missingCore
  deriving DecidableEq

def test (mode : Mode) (C Q : Clause) : Bool :=
  match mode with
  | .equivalent => ExecCNF.equivalent C Q
  | .strictSubset => ExecCNF.strictSubset C Q
  | .missingCore => !(ExecCNF.subset Q C)

def resultRegister : Mode → Fin 15
  | .equivalent => 10
  | .strictSubset => 11
  | .missingCore => 9

def regPort (i : Fin 12) : Fin 15 := Fin.castAdd 3 i
def stackPort (i : Fin 10) : Fin 12 := Fin.castAdd 2 i

theorem regPort_injective : Function.Injective regPort := Fin.castAdd_injective 12 3
theorem stackPort_injective : Function.Injective stackPort := Fin.castAdd_injective 10 2

def restrict (d : Data) : State 12 10 := ⟨d.regs ∘ regPort, d.stacks ∘ stackPort⟩

private theorem embed_restrict (d : Data) :
    embedState regPort stackPort d (restrict d) = d := by
  cases d with
  | mk regs stk =>
    unfold embedState restrict
    congr 1
    · funext i
      by_cases h : ∃ j, regPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact regPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stackPort j = i
      · obtain ⟨j, rfl⟩ := h
        exact stackPort_injective.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

def relationProgram := ProgramLinking.liftProgram
  ExecClauseRelationsProgram.program regPort stackPort

def clean (d : Data) : Prop := ∀ i : Fin 8, d.stacks (Fin.castAdd 4 i) = []

theorem relation_eval (C Q : Clause) (d : Data)
    (hc : d.stacks 8 = encodeClause C) (hq : d.stacks 9 = encodeClause Q)
    (hw : clean d) :
    ∃ n ≤ ExecClauseRelationsProgram.bound C Q, ∃ e : Data,
      Eval (.call relationProgram) n d e ∧ clean e ∧
      (∀ mode, e.regs (resultRegister mode) = test mode C Q) ∧
      e.stacks 8 = d.stacks 8 ∧ e.stacks 9 = d.stacks 9 ∧
      e.stacks 10 = d.stacks 10 ∧ e.stacks 11 = d.stacks 11 ∧
      e.regs 12 = d.regs 12 ∧ e.regs 13 = d.regs 13 ∧ e.regs 14 = d.regs 14 := by
  have hclean : ExecClauseRelationsProgram.clean (restrict d) := hw
  obtain ⟨b, ⟨n, hn, ht⟩, hb, heq, hstrict, hframe, hreverse⟩ :=
    ExecClauseRelationsProgram.program_runsIn_all C Q (restrict d) hc hq hclean
  have heval := eval_call_lifted ExecClauseRelationsProgram.program regPort stackPort d
    regPort_injective stackPort_injective ht
  rw [embed_restrict] at heval
  let e := embedState regPort stackPort d b
  have hstack (i : Fin 10) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stackPort_injective i
  have hreg (i : Fin 12) : e.regs (regPort i) = b.regs i :=
    embedState_register _ _ _ _ regPort_injective i
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hstack (Fin.castAdd 2 i)).trans (hb i)
  · intro mode
    cases mode with
    | equivalent => exact (hreg 10).trans heq
    | strictSubset => exact (hreg 11).trans hstrict
    | missingCore => exact (hreg 9).trans hreverse
  · exact (hstack 8).trans (hframe 0)
  · exact (hstack 9).trans (hframe 1)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

abbrev transferProgram : Program 15 12 4 := StackRoutines.transferProgram 11 8 0 1

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 11 8 d.stacks⟩

abbrev transfer : Cmd 15 12 := .call transferProgram

theorem transfer_eval (d : Data) :
    Eval transfer (3 * (d.stacks 11).length + 3) d (transferred d) := by
  have h := StackRoutines.transferProgram_trace (r := 15) (s := 12)
    11 8 0 1 (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  apply Eval.call
  simpa [transferred, transferProgram, StackRoutines.transferResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

abbrev clearCandidate : Cmd 15 12 := .call (StackRoutines.clearProgram 8 0 1)

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 8 d.stacks⟩

theorem clearCandidate_eval (d : Data) :
    Eval clearCandidate (2 * (d.stacks 8).length + 3) d (cleared d) := by
  have h := StackRoutines.clearProgram_trace (r := 15) (s := 12) 8 0 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StructuredProgram.State.withPC,
    StackRoutines.clearProgram, Nat.add_assoc] using hh

def marked (mode : Mode) (d : Data) : Data :=
  ⟨Function.update d.regs 14 (d.regs (resultRegister mode)), d.stacks⟩

theorem mark_eval (mode : Mode) (d : Data) :
    Eval (RecordPrograms.atom (.copy 14 (resultRegister mode))) 1 d (marked mode d) :=
  .base (.atom _ _)

abbrev callback (mode : Mode) : Cmd 15 12 :=
  .seq transfer (.seq (.call relationProgram)
    (.seq (RecordPrograms.atom (.copy 14 (resultRegister mode))) clearCandidate))

def invariant (Q : Clause) (d : Data) : Prop :=
  d.stacks 9 = encodeClause Q ∧ ∀ i : Fin 9, d.stacks (Fin.castAdd 3 i) = []

def perClauseCost (Q : Clause) (bits : List Bool) : ℕ :=
  180 * (bits.length + 1) * ((encodeClause Q).length + 1)

theorem callback_eval (mode : Mode) (C Q : Clause) (d : Data)
    (hp : d.stacks 11 = (encodeClause C).reverse) (valid : invariant Q d) :
    ∃ n ≤ perClauseCost Q (encodeClause C), ∃ e : Data,
      Eval (callback mode) n d e ∧ invariant Q e ∧ e.regs 14 = test mode C Q ∧
      e.stacks 10 = d.stacks 10 ∧ e.stacks 11 = [] ∧
      e.regs 12 = d.regs 12 ∧ e.regs 13 = d.regs 13 := by
  obtain ⟨hq, hw⟩ := valid
  have h8 : d.stacks 8 = [] := hw 8
  have hc : (transferred d).stacks 8 = encodeClause C := by
    simp [transferred, StackRoutines.transferStacks, hp, h8]
  have hq' : (transferred d).stacks 9 = encodeClause Q := by
    simpa [transferred, StackRoutines.transferStacks] using hq
  have hw' : clean (transferred d) := by
    intro i
    have h := hw (Fin.castAdd 1 i)
    have hcast : Fin.castAdd 3 (Fin.castAdd 1 i) = Fin.castAdd 4 i := Fin.ext rfl
    rw [hcast] at h
    have hi8 : Fin.castAdd 4 i ≠ (8 : Fin 12) := by
      intro h
      have hv : i.val = 8 := congrArg Fin.val h
      omega
    have hi11 : Fin.castAdd 4 i ≠ (11 : Fin 12) := by
      intro h
      have hv : i.val = 11 := congrArg Fin.val h
      omega
    simpa [transferred, StackRoutines.transferStacks, hi8, hi11] using h
  obtain ⟨n, hn, e, he, hclean, hanswer, h8e, h9e, h10e, h11e, h12e, h13e, h14e⟩ :=
    relation_eval C Q (transferred d) hc hq' hw'
  let result := cleared (marked mode e)
  let count := (3 * (d.stacks 11).length + 3) +
    (n + (1 + (2 * (e.stacks 8).length + 3)))
  refine ⟨count, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [count, perClauseCost]
    rw [hp, h8e, hc]
    simp only [List.length_reverse]
    dsimp [ExecClauseRelationsProgram.bound, encodeClause] at hn ⊢
    have hfactor : (Encoding.encodeList id C).length + 1 ≤
        ((Encoding.encodeList id C).length + 1) *
          ((Encoding.encodeList id Q).length + 1) := by
      calc
        (Encoding.encodeList id C).length + 1 =
            ((Encoding.encodeList id C).length + 1) * 1 := by omega
        _ ≤ ((Encoding.encodeList id C).length + 1) *
            ((Encoding.encodeList id Q).length + 1) := by
          exact Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.mul_assoc] at hn ⊢
    omega
  · exact Eval.seq (transfer_eval d)
      (Eval.seq he (Eval.seq (mark_eval mode e) (clearCandidate_eval (marked mode e))))
  · refine ⟨?_, ?_⟩
    · simpa [result, cleared, marked, StackRoutines.clearStacks] using h9e.trans hq'
    · intro i
      by_cases hi : i.val = 8
      · have hi' : Fin.castAdd 3 i = (8 : Fin 12) := Fin.ext hi
        simp [hi', result, cleared, StackRoutines.clearStacks]
      · have hil : i.val < 8 := by omega
        have h := hclean ⟨i.val, hil⟩
        have hcast : Fin.castAdd 4 (⟨i.val, hil⟩ : Fin 8) =
            Fin.castAdd 3 i := Fin.ext rfl
        rw [hcast] at h
        have hi8 : Fin.castAdd 3 i ≠ (8 : Fin 12) := by
          intro h
          have hv : i.val = 8 := congrArg Fin.val h
          omega
        simpa [result, cleared, marked, StackRoutines.clearStacks, hi8] using h
  · simpa [result, cleared, readRegs, marked] using hanswer mode
  · simpa [result, cleared, marked, StackRoutines.clearStacks, transferred,
      StackRoutines.transferStacks] using h10e
  · simpa [result, cleared, marked, StackRoutines.clearStacks, transferred,
      StackRoutines.transferStacks] using h11e
  · simpa [result, cleared, marked, readRegs, transferred] using h12e
  · simpa [result, cleared, marked, readRegs, transferred] using h13e

def ports : RecordPrograms.Ports 15 12 where
  tag := 12
  present := 13
  found := 14
  source := 10
  payload := 11
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem callback_contract (mode : Mode) (Q : Clause) :
    RecordMappedPrograms.Contract ports (callback mode) encodeClause
      (fun C => test mode C Q) (fun C => perClauseCost Q (encodeClause C)) (invariant Q) := by
  intro C tail base hbase
  let d := RecordPrograms.state ports base false true false tail (encodeClause C).reverse
  have hd10 : d.stacks 10 = tail := by simp [d, RecordPrograms.state, ports]
  have hd11 : d.stacks 11 = (encodeClause C).reverse := by
    simp [d, RecordPrograms.state, ports]
  have hd12 : d.regs 12 = false := by simp [d, RecordPrograms.state, ports]
  have hd13 : d.regs 13 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant Q d := by
    refine ⟨?_, ?_⟩
    · simpa [d, RecordPrograms.state, ports] using hbase.1
    · intro i
      have hi10 : Fin.castAdd 3 i ≠ (10 : Fin 12) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      have hi11 : Fin.castAdd 3 i ≠ (11 : Fin 12) := by
        intro h
        have hv : i.val = 11 := congrArg Fin.val h
        omega
      simpa [d, RecordPrograms.state, ports, hi10, hi11] using hbase.2 i
  obtain ⟨n, hn, e, he, hv, ha, h10, h11, h12, h13⟩ := callback_eval mode C Q d hd11 hv
  have heState : RecordPrograms.state ports e false true (test mode C Q) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h12.trans hd12) (h13.trans hd13)
      ha (h10.trans hd10) h11
  refine ⟨n, e, hn, hv, ?_⟩
  rw [heState]
  exact he

def encodeFormula (F : Formula) : List Bool := Encoding.encodeList encodeClause F

abbrev command (mode : Mode) : Cmd 15 12 :=
  .seq (RecordPrograms.iterate ports (callback mode)) (RecordPrograms.atom (.push 11 14))

theorem emit_eval (base : Data) (answer : Bool) (source : List Bool) :
    Eval (RecordPrograms.atom (.push 11 14)) 1
      (RecordPrograms.state ports base false true answer source [])
      (RecordPrograms.state ports base false true answer source [answer]) := by
  have h : (StructuredProgram.Atom.push (r := 15) (s := 12) 11 14).eval
      (RecordPrograms.state ports base false true answer source []) =
      RecordPrograms.state ports base false true answer source [answer] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  rw [← h]
  exact .base (.atom _ _)

theorem command_eval (mode : Mode) (F : Formula) (Q : Clause) (suffix : List Bool)
    (base : Data) (valid : invariant Q base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data),
      n ≤ 4 + RecordMappedPrograms.budget encodeClause
        (fun C => perClauseCost Q (encodeClause C)) F ∧ invariant Q next ∧
      Eval (command mode) n
        (RecordPrograms.state ports base v pr f (encodeFormula F ++ suffix) [])
        (RecordPrograms.state ports next false true (F.any (fun C => test mode C Q))
          (RecordMappedPrograms.unread encodeClause (fun C => test mode C Q) F suffix)
          [F.any (fun C => test mode C Q)]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordMappedPrograms.iterate_run ports (callback mode)
    encodeClause (fun C => test mode C Q) (fun C => perClauseCost Q (encodeClause C))
    (invariant Q) (callback_contract mode Q) F suffix base valid v pr f
  exact ⟨n + 1, next, by omega, hnext, Eval.seq he (emit_eval _ _ _)⟩

theorem budget_le (F : Formula) (Q : Clause) :
    4 + RecordMappedPrograms.budget encodeClause
        (fun C => perClauseCost Q (encodeClause C)) F ≤
      400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) := by
  have hb := RecordMappedPrograms.program_budget_le_input encodeClause
    (fun C => perClauseCost Q (encodeClause C)) F
    (180 * ((encodeClause Q).length + 1)) (180 * ((encodeClause Q).length + 1)) (by
      intro C _
      dsimp [perClauseCost]
      nlinarith)
  dsimp [encodeFormula] at ⊢
  nlinarith

/-- All runtime clauses and list lengths are stored in Boolean stacks; only
the three-element mode is selected when the fixed program is built. -/
def program (mode : Mode) := compiled (command mode) 10 11

def bound (F : Formula) (Q : Clause) : ℕ :=
  400 * ((encodeClause Q).length + 1) * ((encodeFormula F).length + 1) + 1

theorem program_call (mode : Mode) (F : Formula) (Q : Clause) (d : Data)
    (hs : d.stacks 10 = encodeFormula F) (hp : d.stacks 11 = [])
    (hv : invariant Q d) :
    ∃ n ≤ bound F Q, ∃ e : Data,
      Eval (.call (program mode)) n d e ∧ invariant Q e ∧
      e.regs 14 = F.any (fun C => test mode C Q) ∧
      e.stacks 11 = [F.any (fun C => test mode C Q)] ∧
      (e.stacks 10).length ≤ (encodeFormula F).length := by
  obtain ⟨n, next, hn, hnext, he⟩ := command_eval mode F Q [] d hv
    (d.regs 12) (d.regs 13) (d.regs 14)
  have hstart : RecordPrograms.state ports d (d.regs 12) (d.regs 13) (d.regs 14)
      (encodeFormula F ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · rw [show ports.source = (10 : Fin 12) from rfl]
      simpa only [List.append_nil] using hs
    · exact hp
  rw [hstart] at he
  have ht := compiled_halt_trace he 10 11
  refine ⟨n + 1, ?_, _, Eval.call (program mode) ht, ?_, ?_, ?_, ?_⟩
  · have hb := budget_le F Q
    dsimp [bound]
    omega
  · refine ⟨?_, ?_⟩
    · simpa [RecordPrograms.state, ports] using hnext.1
    · intro i
      have hi10 : Fin.castAdd 3 i ≠ (10 : Fin 12) := by
        intro h
        have hv : i.val = 10 := congrArg Fin.val h
        omega
      have hi11 : Fin.castAdd 3 i ≠ (11 : Fin 12) := by
        intro h
        have hv : i.val = 11 := congrArg Fin.val h
        omega
      simpa [RecordPrograms.state, ports, hi10, hi11] using hnext.2 i
  · simp [RecordPrograms.state, ports]
  · simp [RecordPrograms.state, ports]
  · simpa [RecordPrograms.state, ports, encodeFormula] using
      RecordMappedPrograms.unread_length_le encodeClause (fun C => test mode C Q) F []

theorem missingCore_false_iff (F : Formula) (Q : Clause) :
    F.any (fun C => test .missingCore C Q) = false ↔
      ∀ C ∈ F, ExecCNF.clauseSet Q ⊆ ExecCNF.clauseSet C := by
  simp [test, List.any_eq_false, ExecCNF.subset_true]

theorem equivalent_true_iff (F : Formula) (Q : Clause) :
    F.any (fun C => test .equivalent C Q) = true ↔
      ∃ C ∈ F, ExecCNF.clauseSet C = ExecCNF.clauseSet Q := by
  simp [test, List.any_eq_true]

theorem strictSubset_true_iff (F : Formula) (Q : Clause) :
    F.any (fun C => test .strictSubset C Q) = true ↔
      ∃ C ∈ F, ExecCNF.clauseSet C ⊂ ExecCNF.clauseSet Q := by
  simp [test, List.any_eq_true]

end SubexponentialSAT.ExecClauseRelationScan

end OAI.Algorithms
