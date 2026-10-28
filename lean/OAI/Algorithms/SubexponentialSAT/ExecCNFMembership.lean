import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.ExecCNFRecords
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost39Lift
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# Encoded CNF membership building blocks

Fixed ports: source 0, reversed current payload 1, preserved reversed query 2,
query copy 3, and temporary stack 4. Register 4 is the answer; registers 5 and
6 are the outer-list tag and presence flag. Registers 0--3 are work bits.
-/

namespace SubexponentialSAT.ExecCNFMembership

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredCalls

abbrev Data := State 7 5

/-- The query remains on port 2; a forward-order copy is made on port 3. -/
abbrev copyQueryProgram : Program 7 5 8 := StackRoutines.copyProgram 2 3 4 0 1

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 2 3 d.stacks⟩

abbrev copyQuery : Cmd 7 5 := .call copyQueryProgram

theorem copyQuery_eval (d : Data) (htmp : d.stacks 4 = []) :
    Eval copyQuery (7 * (d.stacks 2).length + 5) d (copied d) := by
  have h := StackRoutines.copyProgram_trace (r := 7) (s := 5)
    2 3 4 0 1 (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp
  have hh : step copyQueryProgram
      (StackRoutines.copyResult 7 2 3 0 1 d.regs d.stacks) =
      some ((copied d).withPC none) := by
    simp [step, StackRoutines.copyResult,
      copied, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  change Computation.Trace (step copyQueryProgram) (7 * (d.stacks 2).length + 5)
    (d.withPC (some 0)) ((copied d).withPC none)
  exact h.trans (.cons hh (.refl _))

/-- Clearing is an actual two-instruction loop followed by a halt/return. -/
abbrev clearProgram (port : Fin 5) : Program 7 5 3 := StackRoutines.clearProgram port 0 1

def cleared (port : Fin 5) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

abbrev clear (port : Fin 5) : Cmd 7 5 := .call (clearProgram port)

theorem clear_eval (port : Fin 5) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have h := StackRoutines.clearProgram_trace (r := 7) (s := 5) port 0 1 d.regs d.stacks
  have hh : step (clearProgram port)
      (StackRoutines.clearResult 2 port 0 1 d.regs d.stacks) =
      some ((cleared port d).withPC none) := by
    simp [step, StackRoutines.clearResult,
      cleared, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  change Computation.Trace (step (clearProgram port)) (2 * (d.stacks port).length + 3)
    (d.withPC (some 0)) ((cleared port d).withPC none)
  exact h.trans (.cons hh (.refl _))

@[simp] theorem copied_stack_zero (d : Data) : (copied d).stacks 0 = d.stacks 0 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_one (d : Data) : (copied d).stacks 1 = d.stacks 1 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_two (d : Data) : (copied d).stacks 2 = d.stacks 2 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_three (d : Data) :
    (copied d).stacks 3 = d.stacks 2 ++ d.stacks 3 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_stack_four (d : Data) : (copied d).stacks 4 = d.stacks 4 := by
  simp [copied, StackRoutines.copyStacks]
@[simp] theorem copied_reg_four (d : Data) : (copied d).regs 4 = d.regs 4 := by
  simp [copied, readRegs]
@[simp] theorem copied_reg_five (d : Data) : (copied d).regs 5 = d.regs 5 := by
  simp [copied, readRegs]
@[simp] theorem copied_reg_six (d : Data) : (copied d).regs 6 = d.regs 6 := by
  simp [copied, readRegs]

@[simp] theorem cleared_stack_self (port : Fin 5) (d : Data) :
    (cleared port d).stacks port = [] := by simp [cleared, StackRoutines.clearStacks]

theorem cleared_stack_other (port j : Fin 5) (d : Data) (hne : j ≠ port) :
    (cleared port d).stacks j = d.stacks j := by
  simp [cleared, StackRoutines.clearStacks, hne]

@[simp] theorem cleared_reg_four (port : Fin 5) (d : Data) :
    (cleared port d).regs 4 = d.regs 4 := by simp [cleared, readRegs]
@[simp] theorem cleared_reg_five (port : Fin 5) (d : Data) :
    (cleared port d).regs 5 = d.regs 5 := by simp [cleared, readRegs]
@[simp] theorem cleared_reg_six (port : Fin 5) (d : Data) :
    (cleared port d).regs 6 = d.regs 6 := by simp [cleared, readRegs]


/-- Compare the parsed reversed payload against a fresh copy of the query,
then clear both inspected work strings, including early-mismatch residuals. -/
abbrev callback : Cmd 7 5 :=
  .seq copyQuery
    (.seq (.call SubexponentialSAT.ExecClauseCost.membershipEqProgram) (.seq (clear 1) (clear 3)))

/-- Actual call traces, not a semantic equality instruction, implement the
callback. The preserved query and source suffix make another iteration safe. -/
theorem callback_eval (d : Data) (hcopy : d.stacks 3 = []) (htmp : d.stacks 4 = []) :
    ∃ n ≤ 20 * ((d.stacks 1).length + (d.stacks 2).length + 1), ∃ e : Data,
      Eval callback n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 2) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = [] ∧ e.stacks 4 = [] ∧
      e.regs 5 = d.regs 5 ∧ e.regs 6 = d.regs 6 := by
  obtain ⟨n, hn, e, heval, hanswer, hsource, hquery, htemp, hleft, hright, htag, hpresent⟩ :=
    SubexponentialSAT.ExecClauseCost.membershipEq_eval (copied d)
  simp only [copied_stack_zero, copied_stack_one, copied_stack_two, copied_stack_three,
    copied_stack_four, copied_reg_five, copied_reg_six, hcopy, List.append_nil]
      at hn hanswer hsource hquery htemp hleft hright htag hpresent
  let result := cleared 3 (cleared 1 e)
  let steps := (7 * (d.stacks 2).length + 5) +
    (n + ((2 * (e.stacks 1).length + 3) + (2 * (e.stacks 3).length + 3)))
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps]
    omega
  · apply Eval.seq (copyQuery_eval d htmp)
    apply Eval.seq heval
    apply Eval.seq (clear_eval 1 e)
    simpa [result, cleared, StackRoutines.clearStacks] using clear_eval 3 (cleared 1 e)
  · simpa [result] using hanswer
  · simpa [result, cleared, StackRoutines.clearStacks] using hsource
  · simp [result, cleared, StackRoutines.clearStacks]
  · simpa [result, cleared, StackRoutines.clearStacks] using hquery
  · simp [result]
  · simpa [result, cleared, StackRoutines.clearStacks, htmp] using htemp
  · simpa [result] using htag
  · simpa [result] using hpresent


/-- The runtime query is on stack 2; these ports are fixed for every query. -/
abbrev ports : RecordPrograms.Ports 7 5 where
  tag := 5
  present := 6
  found := 4
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def invariant (query : List Bool) (d : Data) : Prop :=
  d.stacks 2 = query.reverse ∧ d.stacks 3 = [] ∧ d.stacks 4 = []

def perRecordCost (query bits : List Bool) : ℕ := 20 * (bits.length + query.length + 1)

theorem callback_contract (query : List Bool) :
    RecordPrograms.CallbackContract ports callback (fun bits => decide (bits = query))
      (perRecordCost query) (invariant query) := by
  intro bits tail base hbase
  rcases hbase with ⟨hquery, hcopy, htmp⟩
  let d := RecordPrograms.state ports base false true false tail bits.reverse
  have hd0 : d.stacks 0 = tail := by simp [d, RecordPrograms.state ]
  have hd1 : d.stacks 1 = bits.reverse := by simp [d, RecordPrograms.state ]
  have hd2 : d.stacks 2 = query.reverse := by simp [d, RecordPrograms.state, hquery]
  have hd3 : d.stacks 3 = [] := by simp [d, RecordPrograms.state, hcopy]
  have hd4 : d.stacks 4 = [] := by simp [d, RecordPrograms.state, htmp]
  have hd5 : d.regs 5 = false := by simp [d, RecordPrograms.state ]
  have hd6 : d.regs 6 = true := by simp [d, RecordPrograms.state ]
  obtain ⟨n, hn, e, he, ha, hs, hp, hq, hc, ht, hv, hpr⟩ := callback_eval d hd3 hd4
  have heq : e.regs 4 = decide (bits = query) := by simpa [hd1, hd2] using ha
  have es : e.stacks 0 = tail := hs.trans hd0
  have ev : e.regs 5 = false := hv.trans hd5
  have epr : e.regs 6 = true := hpr.trans hd6
  have eState : RecordPrograms.state ports e false true (decide (bits = query)) tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ ev epr heq es hp
  refine ⟨n, e, ?_, ⟨hq.trans hd2, hc, ht⟩, ?_⟩
  · simpa [perRecordCost, hd1, hd2] using hn
  · rw [eState]
    exact he

/-- Coarse polynomial bound for the iterator's complete per-record budget. -/
theorem budget_le (query : List Bool) (records : List (List Bool)) :
    3 + RecordPrograms.budget (perRecordCost query) records ≤
      (20 * query.length + 30) * (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.budget, Encoding.encodeList]
  | cons bits rest ih =>
    have hstep : 6 * bits.length + perRecordCost query bits + 7 ≤
        (20 * query.length + 30) * (2 * bits.length + 2) := by
      simp only [perRecordCost, Nat.mul_add, Nat.add_mul, Nat.mul_one]
      omega
    simp only [RecordPrograms.budget, Encoding.length_encodeList_cons, id_eq]
    calc
      3 + (6 * bits.length + perRecordCost query bits + 7 +
          RecordPrograms.budget (perRecordCost query) rest)
          = (6 * bits.length + perRecordCost query bits + 7) +
              (3 + RecordPrograms.budget (perRecordCost query) rest) := by omega
      _ ≤ (20 * query.length + 30) * (2 * bits.length + 2) +
          (20 * query.length + 30) * (Encoding.encodeList id rest).length :=
        Nat.add_le_add hstep ih
      _ = (20 * query.length + 30) *
          (2 * bits.length + 2 + (Encoding.encodeList id rest).length) := by
        simp [Nat.mul_add, Nat.add_assoc]


/-- The emitted bit is in stack 1. The encoded source is scanned destructively,
while stack 2 retains the reversed runtime query. -/
abbrev membership : Cmd 7 5 :=
  .seq (RecordPrograms.iterate ports callback) (RecordPrograms.atom (.push 1 4))

theorem any_eq_membership (query : List Bool) (records : List (List Bool)) :
    records.any (fun bits => decide (bits = query)) = decide (query ∈ records) := by
  induction records with
  | nil => simp
  | cons bits rest ih =>
      rw [List.any_cons, ih]
      simp [eq_comm]

theorem emit_eval (base : Data) (answer : Bool) (source : List Bool) :
    Eval (RecordPrograms.atom (.push 1 4)) 1
      (RecordPrograms.state ports base false true answer source [])
      (RecordPrograms.state ports base false true answer source [answer]) := by
  have h : (StructuredProgram.Atom.push (r := 7) (s := 5) 1 4).eval
      (RecordPrograms.state ports base false true answer source []) =
      RecordPrograms.state ports base false true answer source [answer] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
      RecordPrograms.state ]
  rw [← h]
  exact .base (.atom _ _)

theorem membership_eval (query : List Bool) (records : List (List Bool))
    (suffix : List Bool) (base : Data) (valid : invariant query base) (v pr f : Bool) :
    ∃ (n : ℕ) (next : Data), n ≤ 4 + RecordPrograms.budget (perRecordCost query) records ∧
      invariant query next ∧
      Eval membership n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (RecordPrograms.state ports next false true (decide (query ∈ records))
          (RecordPrograms.unread (fun bits => decide (bits = query)) records suffix)
          [decide (query ∈ records)]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordPrograms.iterate_run ports callback
    (fun bits => decide (bits = query)) (perRecordCost query) (invariant query)
    (callback_contract query) records suffix base valid v pr f
  rw [any_eq_membership] at he
  exact ⟨n + 1, next, by omega, hnext, Eval.seq he (emit_eval _ _ _)⟩

/-- This instruction table has fixed size, independent of both runtime inputs. -/
def membershipProgram := compiled membership 0 1

theorem membership_runsIn (query : List Bool) (records : List (List Bool))
    (suffix : List Bool) (base : Data) (valid : invariant query base) (v pr f : Bool) :
    ∃ next : Data, invariant query next ∧
      RunsIn membershipProgram
        ((20 * query.length + 30) * (Encoding.encodeList id records).length + 2)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id records ++ suffix) []).withPC (some membershipProgram.entry))
        ((RecordPrograms.state ports next false true (decide (query ∈ records))
          (RecordPrograms.unread (fun bits => decide (bits = query)) records suffix)
          [decide (query ∈ records)]).withPC none) := by
  obtain ⟨n, next, hn, hnext, he⟩ := membership_eval query records suffix base valid v pr f
  refine ⟨next, hnext, n + 1, ?_, compiled_halt_trace he 0 1⟩
  have hbudget := budget_le query records
  omega


/-- Single-tape input: one framed query, followed by the framed record list. -/
def rawInput (query : List Bool) (records : List (List Bool)) : List Bool :=
  Encoding.frame query ++ Encoding.encodeList id records

def queryPorts : RecordPrograms.Ports 7 5 := { ports with
  payload := 2
  source_ne_payload := by decide }

def loaded (query : List Bool) (records : List (List Bool)) : Data :=
  RecordPrograms.state queryPorts (StructuredProgram.ioState 0 [])
    false true false (Encoding.encodeList id records) query.reverse

theorem load_query_eval (query : List Bool) (records : List (List Bool)) :
    Eval (RecordPrograms.reader queryPorts) (6 * query.length + 4)
      (StructuredProgram.ioState 0 (rawInput query records)) (loaded query records) := by
  have h := RecordPrograms.reader_eval queryPorts
    (StructuredProgram.ioState (r := 7) (s := 5) 0 []) query
    (Encoding.encodeList id records) [] false false false
  have hs : RecordPrograms.state queryPorts (StructuredProgram.ioState 0 [])
      false false false (rawInput query records) [] =
      StructuredProgram.ioState 0 (rawInput query records) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ queryPorts, ports ]
    · funext i
      fin_cases i <;> simp [ queryPorts, ports ]
  dsimp only [rawInput] at hs
  rw [hs] at h
  simpa only [rawInput, List.append_nil, loaded] using h

theorem loaded_invariant (query : List Bool) (records : List (List Bool)) :
    invariant query (loaded query records) := by
  simp [invariant, loaded, RecordPrograms.state, queryPorts ]

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool))
    (suffix : List Bool) :
    (RecordPrograms.unread test records suffix).length ≤
      (Encoding.encodeList id records).length + suffix.length := by
  induction records with
  | nil => simp [RecordPrograms.unread, Encoding.encodeList]
  | cons bits rest ih =>
      simp only [RecordPrograms.unread, Encoding.length_encodeList_cons, id_eq]
      split
      · simp only [List.length_append]
        omega
      · omega

private def setFalse (i : Fin 7) (d : Data) : Data :=
  (StructuredProgram.Atom.set i false).eval d

private theorem setFalse_eval (i : Fin 7) (d : Data) :
    Eval (RecordPrograms.atom (.set i false)) 1 d (setFalse i d) :=
  .base (.atom _ _)

abbrev resetRegisters : Cmd 7 5 :=
  .seq (RecordPrograms.atom (.set 0 false))
  (.seq (RecordPrograms.atom (.set 1 false))
  (.seq (RecordPrograms.atom (.set 2 false))
  (.seq (RecordPrograms.atom (.set 3 false))
  (.seq (RecordPrograms.atom (.set 4 false))
  (.seq (RecordPrograms.atom (.set 5 false))
        (RecordPrograms.atom (.set 6 false)))))))

theorem resetRegisters_eval (d : Data) :
    Eval resetRegisters 7 d ⟨fun _ => false, d.stacks⟩ := by
  have h := Eval.seq (setFalse_eval 0 d)
    (Eval.seq (setFalse_eval 1 (setFalse 0 d))
    (Eval.seq (setFalse_eval 2 (setFalse 1 (setFalse 0 d)))
    (Eval.seq (setFalse_eval 3 (setFalse 2 (setFalse 1 (setFalse 0 d))))
    (Eval.seq (setFalse_eval 4 (setFalse 3 (setFalse 2 (setFalse 1 (setFalse 0 d)))))
    (Eval.seq (setFalse_eval 5 (setFalse 4 (setFalse 3 (setFalse 2 (setFalse 1 (setFalse 0 d))))))
      (setFalse_eval 6 (setFalse 5 (setFalse 4 (setFalse 3 (setFalse 2 (setFalse 1 (setFalse 0 d))))))))))))
  have hs : setFalse 6 (setFalse 5 (setFalse 4 (setFalse 3
      (setFalse 2 (setFalse 1 (setFalse 0 d)))))) = ⟨fun _ => false, d.stacks⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · rfl
  simpa only [resetRegisters, hs] using h

/-- Discard the unscanned suffix and retained query after emitting the answer. -/
abbrev cleanup : Cmd 7 5 := .seq (clear 0) (.seq (clear 2) resetRegisters)

theorem cleanup_eval (d : Data) (answer : Bool) (h1 : d.stacks 1 = [answer])
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    Eval cleanup (2 * (d.stacks 0).length + 2 * (d.stacks 2).length + 13)
      d (StructuredProgram.ioState 1 [answer]) := by
  have h := Eval.seq (clear_eval 0 d)
    (Eval.seq (clear_eval 2 (cleared 0 d)) (resetRegisters_eval (cleared 2 (cleared 0 d))))
  have hs : (⟨fun _ => false, (cleared 2 (cleared 0 d)).stacks⟩ : Data) =
      StructuredProgram.ioState 1 [answer] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [cleared, StackRoutines.clearStacks,
        h1, h3, h4]
  have hc : (2 * (d.stacks 0).length + 3) +
      ((2 * ((cleared 0 d).stacks 2).length + 3) + 7) =
      2 * (d.stacks 0).length + 2 * (d.stacks 2).length + 13 := by
    rw [cleared_stack_other 0 2 d (by decide)]
    omega
  simpa only [cleanup, hc, hs] using h

abbrev rawMembership : Cmd 7 5 :=
  .seq (RecordPrograms.reader queryPorts) (.seq membership cleanup)

def rawMembershipProgram := compiled rawMembership 0 1

theorem rawMembership_eval (query : List Bool) (records : List (List Bool)) :
    ∃ n ≤ 100 * ((rawInput query records).length + 1)^2,
      Eval rawMembership n (StructuredProgram.ioState 0 (rawInput query records))
        (StructuredProgram.ioState 1 [decide (query ∈ records)]) := by
  obtain ⟨n, next, hn, hnext, hm⟩ := membership_eval query records [] (loaded query records)
    (loaded_invariant query records) false true false
  have hstart : RecordPrograms.state ports (loaded query records) false true false
      (Encoding.encodeList id records ++ []) [] = loaded query records := by
    apply RecordPrograms.state_eq_self <;>
      simp [loaded, RecordPrograms.state, queryPorts ]
  rw [hstart] at hm
  let result := RecordPrograms.state ports next false true (decide (query ∈ records))
    (RecordPrograms.unread (fun bits => decide (bits = query)) records [])
    [decide (query ∈ records)]
  have hr0 : result.stacks 0 = RecordPrograms.unread (fun bits => decide (bits = query)) records [] := by
    simp [result, RecordPrograms.state ]
  have hr1 : result.stacks 1 = [decide (query ∈ records)] := by
    simp [result, RecordPrograms.state ]
  have hr2 : result.stacks 2 = query.reverse := by
    simpa [result, RecordPrograms.state, ports] using hnext.1
  have hr3 : result.stacks 3 = [] := by
    simpa [result, RecordPrograms.state, ports] using hnext.2.1
  have hr4 : result.stacks 4 = [] := by
    simpa [result, RecordPrograms.state, ports] using hnext.2.2
  refine ⟨(6 * query.length + 4) +
    (n + (2 * (result.stacks 0).length + 2 * (result.stacks 2).length + 13)), ?_,
    Eval.seq (load_query_eval query records) (Eval.seq hm (cleanup_eval result _ hr1 hr3 hr4))⟩
  have hb := budget_le query records
  have hu := unread_length_le (fun bits => decide (bits = query)) records []
  simp only [List.length_nil, Nat.add_zero] at hu
  simp only [hr0, hr2, List.length_reverse, rawInput, List.length_append, Encoding.length_frame]
  nlinarith

theorem rawMembership_runsIn (query : List Bool) (records : List (List Bool)) :
    RunsIn rawMembershipProgram (100 * ((rawInput query records).length + 1)^2 + 1)
      (initial rawMembershipProgram (rawInput query records))
      (terminal rawMembershipProgram [decide (query ∈ records)]) := by
  obtain ⟨n, hn, he⟩ := rawMembership_eval query records
  exact ⟨n + 1, by omega, compiled_io_trace 0 1 he⟩

theorem rawMembership_primitive_outputs (query : List Bool) (records : List (List Bool)) :
    (primitive rawMembershipProgram).OutputsInTime (rawInput query records)
      (decide (query ∈ records))
      (primitiveOverhead rawMembershipProgram *
        (100 * ((rawInput query records).length + 1)^2 + 1)) :=
  BitProgram.primitive_outputs rawMembershipProgram (rawMembership_runsIn query records)

theorem natMembership_eq_contains (a : ℕ) (C : List ℕ) :
    decide (Encoding.encodeNat a ∈ C.map Encoding.encodeNat) = ExecCNF.contains a C := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ExecCNF.contains_true]
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp h
    exact Encoding.encodeNat_injective hba ▸ hb
  · intro h
    exact List.mem_map.mpr ⟨a, h, rfl⟩

theorem encodeList_map_encodeNat (C : List ℕ) :
    Encoding.encodeList id (C.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat C := by
  induction C with
  | nil => rfl
  | cons a C ih => simp [Encoding.encodeList, ih]

def literalInput (a : ℕ) (C : List ℕ) : List Bool :=
  Encoding.frame (Encoding.encodeNat a) ++ Encoding.encodeList Encoding.encodeNat C

theorem rawInput_literal (a : ℕ) (C : List ℕ) :
    rawInput (Encoding.encodeNat a) (C.map Encoding.encodeNat) = literalInput a C := by
  simp [rawInput, literalInput, encodeList_map_encodeNat]

/-- The concrete bit program implements the earlier executable literal scan.
Arbitrary natural literal codes are compared through their actual encodings. -/
theorem literal_primitive_contains (a : ℕ) (C : List ℕ) :
    (primitive rawMembershipProgram).OutputsInTime (literalInput a C) (ExecCNF.contains a C)
      (primitiveOverhead rawMembershipProgram * (100 * ((literalInput a C).length + 1)^2 + 1)) := by
  simpa only [natMembership_eq_contains, rawInput_literal] using
    rawMembership_primitive_outputs (Encoding.encodeNat a) (C.map Encoding.encodeNat)

end SubexponentialSAT.ExecCNFMembership

end OAI.Algorithms
