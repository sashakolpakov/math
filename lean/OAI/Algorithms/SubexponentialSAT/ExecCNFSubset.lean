import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFMembership
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Actual encoded clause subset testing

The fixed program uses ten Boolean registers and eight Boolean stacks. The
source clause is scanned destructively on stack 0. Stack 2 preserves the entire
encoded target clause. All comparisons use the proved encoded membership
program, after a real preserving copy of the target.
-/
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 8

abbrev copyTargetProgram : Program 10 8 8 := StackRoutines.copyProgram 2 3 7 0 1

abbrev copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 3 d.stacks⟩

abbrev copyTarget : Cmd 10 8 := .call copyTargetProgram

theorem copyTarget_eval (d : Data) (htmp : d.stacks 7 = []) :
    Eval copyTarget (7 * (d.stacks 2).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 10) (s := 8)
    2 3 7 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh : step copyTargetProgram
      (StackRoutines.copyResult 7 2 3 0 1 d.regs d.stacks) =
      some ((copied d).withPC none) := by
    simp [step, StackRoutines.copyResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [copyTargetProgram, copied, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

abbrev clearProgram (port : Fin 8) : Program 10 8 3 := StackRoutines.clearProgram port 0 1

abbrev cleared (port : Fin 8) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev clear (port : Fin 8) : Cmd 10 8 := .call (clearProgram port)

theorem clear_eval (port : Fin 8) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 10) (s := 8) port 0 1 d.regs d.stacks
  have hh : step (clearProgram port)
      (StackRoutines.clearResult 2 port 0 1 d.regs d.stacks) =
      some ((cleared port d).withPC none) := by
    simp [step, StackRoutines.clearResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [clearProgram, cleared, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

def memberReg (i : Fin 7) : Fin 10 := Fin.castAdd 3 i

def memberStack (i : Fin 5) : Fin 8 :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 1
  | 3 => 5
  | _ => 6

def memberProgram := ProgramLinking.liftProgram
  ExecCNFMembership.membershipProgram memberReg memberStack

abbrev memberCall : Cmd 10 8 := .call memberProgram

theorem memberReg_injective : Function.Injective memberReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 10 => i.val) h

theorem memberStack_injective : Function.Injective memberStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [memberStack]

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stkValues =>
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

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread, Encoding.encodeList]
  | cons x xs ih =>
    cases h : test x <;>
      simp [RecordPrograms.unread, h, Encoding.length_encodeList_cons] ; omega

/-- The real membership program lifted into the subset caller. Only its assigned
ports change; its output bit and residual sizes are explicit. -/
theorem memberCall_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hsrc : d.stacks 3 = Encoding.encodeList id records)
    (hquery : d.stacks 1 = query.reverse) (hout : d.stacks 4 = [])
    (hcopy : d.stacks 5 = []) (htmp : d.stacks 6 = []) :
    ∃ n ≤ (20 * query.length + 30) * (Encoding.encodeList id records).length + 2,
      ∃ e : Data, Eval memberCall n d e ∧
      e.regs 4 = decide (query ∈ records) ∧
      (e.stacks 3).length ≤ (Encoding.encodeList id records).length ∧
      e.stacks 4 = [decide (query ∈ records)] ∧ e.stacks 1 = query.reverse ∧
      e.stacks 5 = [] ∧ e.stacks 6 = [] ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧ e.stacks 7 = d.stacks 7 ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  let a : State 7 5 := ⟨d.regs ∘ memberReg, d.stacks ∘ memberStack⟩
  have hvalid : ExecCNFMembership.invariant query a := by
    exact ⟨hquery, hcopy, htmp⟩
  have hstart : RecordPrograms.state ExecCNFMembership.ports a
      (a.regs 5) (a.regs 6) (a.regs 4) (Encoding.encodeList id records ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, memberStack] using hsrc
    · exact hout
  obtain ⟨next, hnext, n, hn, ht⟩ := ExecCNFMembership.membership_runsIn
    query records [] a hvalid (a.regs 5) (a.regs 6) (a.regs 4)
  rw [hstart] at ht
  let b := RecordPrograms.state ExecCNFMembership.ports next false true
    (decide (query ∈ records)) (RecordPrograms.unread (fun bits => decide (bits = query)) records [])
    [decide (query ∈ records)]
  have heval := eval_call_lifted ExecCNFMembership.membershipProgram memberReg memberStack d
    memberReg_injective memberStack_injective ht
  have hea : embedState memberReg memberStack d a = d :=
    embed_restricted _ _ memberReg_injective memberStack_injective d
  rw [hea] at heval
  let e := embedState memberReg memberStack d b
  have hstack (i : Fin 5) : e.stacks (memberStack i) = b.stacks i :=
    embedState_stack _ _ _ _ memberStack_injective i
  have hreg (i : Fin 7) : e.regs (memberReg i) = b.regs i :=
    embedState_register _ _ _ _ memberReg_injective i
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e.regs (memberReg 4) = _
    rw [hreg]
    simp [b, RecordPrograms.state ]
  · change (e.stacks (memberStack 0)).length ≤ _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using
      unread_length_le (fun bits => decide (bits = query)) records
  · change e.stacks (memberStack 1) = _
    rw [hstack]
    simp [b, RecordPrograms.state ]
  · change e.stacks (memberStack 2) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.1
  · change e.stacks (memberStack 3) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.2.1
  · change e.stacks (memberStack 4) = _
    rw [hstack]
    simpa [b, RecordPrograms.state, ExecCNFMembership.ports] using hnext.2.2
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

/-- Remember that the current source literal is absent from the target. -/
abbrev mark (d : Data) : Data :=
  ⟨Function.update d.regs 9 (!d.regs 4), d.stacks⟩

theorem mark_eval (d : Data) :
    Eval (RecordPrograms.atom (.bnot 9 4)) 1 d (mark d) := by
  have h : (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 4).eval d = mark d := by
    rfl
  rw [← h]
  exact .base (.atom _ _)

/-- Each source literal invokes a real copy, encoded membership scan, and three
cleanup loops. The instruction sequence is independent of both clauses. -/
abbrev callback : Cmd 10 8 :=
  .seq copyTarget (.seq memberCall
    (.seq (RecordPrograms.atom (.bnot 9 4)) (.seq (clear 3) (.seq (clear 4) (clear 1)))))

def invariant (records : List (List Bool)) (d : Data) : Prop :=
  d.stacks 2 = Encoding.encodeList id records ∧ d.stacks 3 = [] ∧
    d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = [] ∧ d.stacks 7 = []

def perRecordCost (records : List (List Bool)) (bits : List Bool) : ℕ :=
  50 * (bits.length + 1) * ((Encoding.encodeList id records).length + 1)

theorem callback_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hquery : d.stacks 1 = query.reverse) (valid : invariant records d) :
    ∃ n ≤ perRecordCost records query, ∃ e : Data,
      Eval callback n d e ∧ invariant records e ∧
      e.regs 9 = !decide (query ∈ records) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 := by
  rcases valid with ⟨htarget, hsource, hout, hcopy, htemp, hcopyTemp⟩
  have hsrc : (copied d).stacks 3 = Encoding.encodeList id records := by
    simp [ StackRoutines.copyStacks, htarget, hsource]
  have hq : (copied d).stacks 1 = query.reverse := by
    simpa [copied, StackRoutines.copyStacks] using hquery
  have ho : (copied d).stacks 4 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hout
  have hc : (copied d).stacks 5 = [] := by
    simpa [copied, StackRoutines.copyStacks] using hcopy
  have ht : (copied d).stacks 6 = [] := by
    simpa [copied, StackRoutines.copyStacks] using htemp
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, hzero, htwo, hseven, hr7, hr8, hr9⟩ :=
    memberCall_eval query records (copied d) hsrc hq ho hc ht
  let result := cleared 1 (cleared 4 (cleared 3 (mark e)))
  let steps := (7 * (d.stacks 2).length + 5) +
    (n + (1 + ((2 * (e.stacks 3).length + 3) +
      ((2 * (e.stacks 4).length + 3) + (2 * (e.stacks 1).length + 3)))))
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps, perRecordCost]
    rw [htarget, hp, hq]
    simp only [List.length_cons, List.length_nil, List.length_reverse]
    nlinarith
  · apply Eval.seq (copyTarget_eval d hcopyTemp)
    apply Eval.seq he
    apply Eval.seq (mark_eval e)
    apply Eval.seq (clear_eval 3 (mark e))
    apply Eval.seq (clear_eval 4 (cleared 3 (mark e)))
    simpa [result, cleared, StackRoutines.clearStacks, mark] using
      clear_eval 1 (cleared 4 (cleared 3 (mark e)))
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
        StackRoutines.copyStacks, htarget] using htwo
    · simp [result, StackRoutines.clearStacks ]
    · simp [result, StackRoutines.clearStacks ]
    · simpa [result, cleared, StackRoutines.clearStacks, mark] using hc
    · simpa [result, cleared, StackRoutines.clearStacks, mark] using ht
    · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
        StackRoutines.copyStacks, hcopyTemp] using hseven
  · simp [result, readRegs, ha]
  · simpa [result, cleared, StackRoutines.clearStacks, mark, copied,
      StackRoutines.copyStacks] using hzero
  · simp [result, StackRoutines.clearStacks]
  · simpa [result, cleared, readRegs, mark, copied] using hr7
  · simpa [result, cleared, readRegs, mark, copied] using hr8

/-- The outer iterator scans the source clause, stopping at its first literal
that the concrete membership program cannot find in the preserved target. -/
def ports : RecordPrograms.Ports 10 8 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem callback_contract (records : List (List Bool)) :
    RecordPrograms.CallbackContract ports callback (fun bits => !decide (bits ∈ records))
      (perRecordCost records) (invariant records) := by
  intro bits tail base hbase
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state, ports]
  have hd1 : d.stacks 1 = bits.reverse := by simp [d, RecordPrograms.state, ports]
  have hd7 : d.regs 7 = false := by simp [d, RecordPrograms.state, ports]
  have hd8 : d.regs 8 = true := by simp [d, RecordPrograms.state, ports]
  have hv : invariant records d := by
    simpa [invariant, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, hv, ha, hs, hp, h7, h8⟩ := callback_eval bits records d hd1 hv
  have eState : RecordPrograms.state ports e false true (!decide (bits ∈ records)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ (h7.trans hd7) (h8.trans hd8)
      ha (hs.trans hd0) hp
  refine ⟨n, e, hn, hv, ?_⟩
  rw [eState]
  exact he

theorem contains_eq_decide (bits : List Bool) (records : List (List Bool)) :
    ExecCNF.contains bits records = decide (bits ∈ records) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem not_any_missing (source target : List (List Bool)) :
    (!(source.any (fun bits => !decide (bits ∈ target)))) = ExecCNF.subset source target := by
  induction source with
  | nil => rfl
  | cons bits rest ih =>
    simp only [List.any_cons, Bool.not_or, Bool.not_not, ExecCNF.subset,
      contains_eq_decide, ih]

/-- Invert the missing-literal flag and expose the answer as an output bit. -/
abbrev finish : Cmd 10 8 :=
  .seq (RecordPrograms.atom (.bnot 9 9)) (RecordPrograms.atom (.push 1 9))

theorem finish_eval (base : Data) (missing : Bool) (source : List Bool) :
    Eval finish 2 (RecordPrograms.state ports base false true missing source [])
      (RecordPrograms.state ports base false true (!missing) source [!missing]) := by
  have h1 : (StructuredProgram.Atom.bnot (r := 10) (s := 8) 9 9).eval
      (RecordPrograms.state ports base false true missing source []) =
      RecordPrograms.state ports base false true (!missing) source [] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  have h2 : (StructuredProgram.Atom.push (r := 10) (s := 8) 1 9).eval
      (RecordPrograms.state ports base false true (!missing) source []) =
      RecordPrograms.state ports base false true (!missing) source [!missing] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state, ports]
  have he1 : Eval (RecordPrograms.atom (.bnot 9 9)) 1
      (RecordPrograms.state ports base false true missing source [])
      (RecordPrograms.state ports base false true (!missing) source []) := by
    rw [← h1]
    exact .base (.atom _ _)
  have he2 : Eval (RecordPrograms.atom (.push 1 9)) 1
      (RecordPrograms.state ports base false true (!missing) source [])
      (RecordPrograms.state ports base false true (!missing) source [!missing]) := by
    rw [← h2]
    exact .base (.atom _ _)
  exact Eval.seq he1 he2

abbrev subset : Cmd 10 8 := .seq (RecordPrograms.iterate ports callback) finish

theorem subset_eval (source target : List (List Bool)) (suffix : List Bool)
    (base : Data) (valid : invariant target base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data),
      n ≤ 5 + RecordPrograms.budget (perRecordCost target) source ∧
      invariant target next ∧
      Eval subset n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id source ++ suffix) [])
        (RecordPrograms.state ports next false true (ExecCNF.subset source target)
          (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
          [ExecCNF.subset source target]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordPrograms.iterate_run ports callback
    (fun bits => !decide (bits ∈ target)) (perRecordCost target) (invariant target)
    (callback_contract target) source suffix base valid v pr f
  have hf := finish_eval next (source.any (fun bits => !decide (bits ∈ target)))
    (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
  rw [not_any_missing] at hf
  exact ⟨n + 2, next, by omega, hnext, Eval.seq he hf⟩

/-- The bound accounts for every parsed bit, target copy, membership scan,
cleanup instruction, and loop test in the fixed subset program. -/
theorem budget_le (source target : List (List Bool)) :
    3 + RecordPrograms.budget (perRecordCost target) source ≤
      64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length := by
  induction source with
  | nil => simp only [RecordPrograms.budget, Encoding.encodeList, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_zero, Nat.mul_one]; omega
  | cons bits rest ih =>
    have hstep : 6 * bits.length + perRecordCost target bits + 7 ≤
        64 * ((Encoding.encodeList id target).length + 1) * (2 * bits.length + 2) := by
      dsimp [perRecordCost]
      nlinarith
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perRecordCost target bits + 7 +
          RecordPrograms.budget (perRecordCost target) rest)
          = (6 * bits.length + perRecordCost target bits + 7) +
              (3 + RecordPrograms.budget (perRecordCost target) rest) := by omega
      _ ≤ 64 * ((Encoding.encodeList id target).length + 1) * (2 * bits.length + 2) +
          64 * ((Encoding.encodeList id target).length + 1) *
            (Encoding.encodeList id rest).length := Nat.add_le_add hstep ih
      _ = _ := by ring

/-- A single finite instruction table implements all runtime subset instances. -/
def subsetProgram := compiled subset 0 1

theorem subset_runsIn (source target : List (List Bool)) (suffix : List Bool)
    (base : Data) (valid : invariant target base) (v pr f : Bool) :
    ∃ next : Data, invariant target next ∧
      RunsIn subsetProgram
        (64 * ((Encoding.encodeList id target).length + 1) *
          (Encoding.encodeList id source).length + 3)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id source ++ suffix) []).withPC (some subsetProgram.entry))
        ((RecordPrograms.state ports next false true (ExecCNF.subset source target)
          (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source suffix)
          [ExecCNF.subset source target]).withPC none) := by
  obtain ⟨n, next, hn, hnext, he⟩ := subset_eval source target suffix base valid v pr f
  refine ⟨next, hnext, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hb := budget_le source target
  omega

theorem subset_call (source target : List (List Bool)) (d : Data)
    (hsource : d.stacks 0 = Encoding.encodeList id source) (hout : d.stacks 1 = [])
    (valid : invariant target d) :
    ∃ n ≤ 64 * ((Encoding.encodeList id target).length + 1) *
        (Encoding.encodeList id source).length + 3, ∃ e : Data,
      Eval (.call subsetProgram) n d e ∧ invariant target e ∧
      e.regs 9 = ExecCNF.subset source target ∧
      e.stacks 1 = [ExecCNF.subset source target] ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id source).length := by
  obtain ⟨next, hnxt, n, hn, ht⟩ := subset_runsIn source target [] d valid
    (d.regs 7) (d.regs 8) (d.regs 9)
  have hs : RecordPrograms.state ports d (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id source ++ []) [] = d := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [ports] using hsource
    · exact hout
  rw [hs] at ht
  refine ⟨n, hn, _, Eval.call subsetProgram ht, ?_, ?_, ?_, ?_⟩
  · simpa [invariant, RecordPrograms.state, ports] using hnxt
  · simp [RecordPrograms.state, ports]
  · simp [RecordPrograms.state, ports]
  · simpa [RecordPrograms.state, ports] using
      unread_length_le (fun bits => !decide (bits ∈ target)) source

end SubexponentialSAT.ExecCNFSubset
namespace SubexponentialSAT.ExecCNFSubset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The raw input places the entire target record list in a frame, followed by
the source record list. This has a fixed schema independent of either clause. -/
def rawInput (source target : List (List Bool)) : List Bool :=
  Encoding.frame (Encoding.encodeList id target) ++ Encoding.encodeList id source

abbrev loaded (source target : List (List Bool)) : Data :=
  RecordPrograms.state ports (StructuredProgram.ioState 0 []) false true false
    (Encoding.encodeList id source) (Encoding.encodeList id target).reverse

theorem load_target_eval (source target : List (List Bool)) :
    Eval (RecordPrograms.reader ports) (6 * (Encoding.encodeList id target).length + 4)
      (StructuredProgram.ioState 0 (rawInput source target)) (loaded source target) := by
  have h := RecordPrograms.reader_eval ports
    (StructuredProgram.ioState (r := 10) (s := 8) 0 [])
    (Encoding.encodeList id target) (Encoding.encodeList id source) [] false false false
  have hs : RecordPrograms.state ports (StructuredProgram.ioState 0 [])
      false false false (rawInput source target) [] =
      StructuredProgram.ioState 0 (rawInput source target) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ ports ]
    · funext i
      fin_cases i <;> simp [ ports ]
  dsimp only [rawInput] at hs
  rw [hs] at h
  simpa only [List.append_nil, loaded, rawInput] using h

abbrev transferTargetProgram : Program 10 8 4 := StackRoutines.transferProgram 1 2 0 1

abbrev transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 1 2 d.stacks⟩

abbrev transferTarget : Cmd 10 8 := .call transferTargetProgram

theorem transferTarget_eval (d : Data) :
    Eval transferTarget (3 * (d.stacks 1).length + 3) d (transferred d) := by
  have h := StackRoutines.transferProgram_trace (r := 10) (s := 8)
    1 2 0 1 (by decide) (by decide) d.regs d.stacks
  have hh : step transferTargetProgram
      (StackRoutines.transferResult 3 1 2 0 1 d.regs d.stacks) =
      some ((transferred d).withPC none) := by
    simp [step,
      StackRoutines.transferResult, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [transferTargetProgram, transferred, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

theorem transferred_loaded_invariant (source target : List (List Bool)) :
    invariant target (transferred (loaded source target)) := by
  simp [invariant, loaded, StackRoutines.transferStacks,
    RecordPrograms.state, ports ]

abbrev rawSubset : Cmd 10 8 :=
  .seq (RecordPrograms.reader ports) (.seq transferTarget subset)

def rawSubsetProgram := compiled rawSubset 0 1

theorem rawSubset_eval (source target : List (List Bool)) :
    ∃ n ≤ 128 * ((rawInput source target).length + 1)^2, ∃ e : Data,
      Eval rawSubset n (StructuredProgram.ioState 0 (rawInput source target)) e ∧
      e.stacks 1 = [ExecCNF.subset source target] ∧ invariant target e := by
  let ready := transferred (loaded source target)
  obtain ⟨n, next, hn, hnext, hs⟩ := subset_eval source target [] ready
    (transferred_loaded_invariant source target) false true false
  have hstart : RecordPrograms.state ports ready false true false
      (Encoding.encodeList id source ++ []) [] = ready := by
    apply RecordPrograms.state_eq_self <;>
      simp [ready, loaded, StackRoutines.transferStacks,
        RecordPrograms.state, ports, readRegs]
  rw [hstart] at hs
  let result := RecordPrograms.state ports next false true (ExecCNF.subset source target)
    (RecordPrograms.unread (fun bits => !decide (bits ∈ target)) source [])
    [ExecCNF.subset source target]
  refine ⟨(6 * (Encoding.encodeList id target).length + 4) +
    ((3 * ((loaded source target).stacks 1).length + 3) + n), ?_, result,
    Eval.seq (load_target_eval source target) (Eval.seq (transferTarget_eval _) hs), ?_, ?_⟩
  · have hb := budget_le source target
    have hl : ((loaded source target).stacks 1).length =
        (Encoding.encodeList id target).length := by
      simp [loaded, RecordPrograms.state, ports]
    rw [hl]
    simp only [rawInput, List.length_append, Encoding.length_frame]
    nlinarith
  · simp [result, RecordPrograms.state, ports]
  · simpa [result, invariant, RecordPrograms.state, ports] using hnext

/-- The single raw input is parsed by the actual fixed program; no external
preparation of the clause stacks is assumed. The output is marshalled on stack1. -/
theorem rawSubset_runsIn (source target : List (List Bool)) :
    ∃ final : Cfg 10 8 _,
      RunsIn rawSubsetProgram (128 * ((rawInput source target).length + 1)^2 + 1)
        (initial rawSubsetProgram (rawInput source target)) final ∧
      final.pc = none ∧ final.stacks 1 = [ExecCNF.subset source target] := by
  obtain ⟨n, hn, e, he, hout, _⟩ := rawSubset_eval source target
  refine ⟨e.withPC none, ⟨n + 1, by omega, ?_⟩, rfl, hout⟩
  exact compiled_halt_trace he 0 1

theorem rawSubset_primitive_outputs (source target : List (List Bool)) :
    (primitive rawSubsetProgram).OutputsInTime (rawInput source target)
      (ExecCNF.subset source target)
      (primitiveOverhead rawSubsetProgram *
        (128 * ((rawInput source target).length + 1)^2 + 1)) := by
  obtain ⟨final, hrun, hhalt, hout⟩ := rawSubset_runsIn source target
  apply primitive_outputs_of_halted rawSubsetProgram hrun hhalt
  change (final.stacks 1).head? = _
  rw [hout]
  rfl

theorem subset_map_injective {α : Type} [DecidableEq α]
    (encode : α → List Bool) (hinj : Function.Injective encode) (source target : List α) :
    ExecCNF.subset (source.map encode) (target.map encode) = ExecCNF.subset source target := by
  apply Bool.eq_iff_iff.mpr
  simp only [ExecCNF.subset_true, Finset.subset_iff, ExecCNF.mem_clauseSet]
  constructor
  · intro h x hx
    obtain ⟨y, hy, he⟩ := List.mem_map.mp (h (List.mem_map.mpr ⟨x, hx, rfl⟩))
    exact hinj he ▸ hy
  · intro h bits hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map.mpr ⟨x, h hx, rfl⟩

/-- Natural-number literal codes are represented by their actual unary bit
strings, and the machine's answer agrees with the source-level list predicate. -/
theorem natSubset_primitive_outputs (source target : List ℕ) :
    (primitive rawSubsetProgram).OutputsInTime
      (rawInput (source.map Encoding.encodeNat) (target.map Encoding.encodeNat))
      (ExecCNF.subset source target)
      (primitiveOverhead rawSubsetProgram *
        (128 * ((rawInput (source.map Encoding.encodeNat)
          (target.map Encoding.encodeNat)).length + 1)^2 + 1)) := by
  simpa only [subset_map_injective Encoding.encodeNat Encoding.encodeNat_injective] using
    rawSubset_primitive_outputs (source.map Encoding.encodeNat) (target.map Encoding.encodeNat)

/-- The literal-code map is injective, so the same fixed machine implements
clause inclusion for bounded-variable SAT literals. -/
theorem literalSubset_primitive_outputs {n : ℕ}
    (source target : List (SAT.Literal (Fin n))) :
    let encode := Encoding.encodeNat ∘ Encoding.literalCode
    (primitive rawSubsetProgram).OutputsInTime
      (rawInput (source.map encode) (target.map encode))
      (ExecCNF.subset source target)
      (primitiveOverhead rawSubsetProgram *
        (128 * ((rawInput (source.map encode) (target.map encode)).length + 1)^2 + 1)) := by
  dsimp only
  simpa only [subset_map_injective (Encoding.encodeNat ∘ Encoding.literalCode)
    (Encoding.encodeNat_injective.comp Encoding.literalCode_injective)] using
    rawSubset_primitive_outputs (source.map (Encoding.encodeNat ∘ Encoding.literalCode))
      (target.map (Encoding.encodeNat ∘ Encoding.literalCode))

end SubexponentialSAT.ExecCNFSubset

end OAI.Algorithms
