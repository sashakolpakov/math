import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFSubset
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.ProgramEncoding
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

open BitProgram

namespace CountRecords

def cfg {l : ℕ} (pc : Option (Fin l)) (value present : Bool)
    (input output : List Bool) : Cfg 2 2 l :=
  ⟨pc, ParserProgram.pair value present, ParserProgram.pair input output⟩

/-- Count records into a canonical unary field. Payload bits are skipped by
following their escape tags. The same thirteen labels handle every count. -/
abbrev program : Program 2 2 13 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 0 4 10
    | 4 => .set 0 true 5
    | 5 => .push 1 0 6
    | 6 => .pop 0 0 1 7
    | 7 => .branch 0 8 2
    | 8 => .pop 0 0 1 9
    | 9 => .goto 6
    | 10 => .set 0 false 11
    | 11 => .set 1 false 12
    | _ => .halt

theorem start (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 0) value present input output)
      (cfg (some 2) false present input (false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem begin_record (value present : Bool) (input output : List Bool) :
    Trace program 4 (cfg (some 2) value present (true :: input) output)
      (cfg (some 6) true true input (true :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem skip_bit (bit value present : Bool) (input output : List Bool) :
    Trace program 4 (cfg (some 6) value present (true :: bit :: input) output)
      (cfg (some 6) bit true input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem skip_end (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 6) value present (false :: input) output)
      (cfg (some 2) false true input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem frame_trace (bits rest output : List Bool) (value present : Bool) :
    Trace program (4 * bits.length + 2)
      (cfg (some 6) value present (Encoding.frame bits ++ rest) output)
      (cfg (some 2) false true rest output) := by
  induction bits generalizing value present with
  | nil => simpa [Encoding.frame] using skip_end value present rest output
  | cons bit bits ih =>
      have h := (skip_bit bit value present (Encoding.frame bits ++ rest) output).trans
        (ih bit true)
      simpa [Encoding.frame, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h

theorem record_trace (bits rest output : List Bool) (value present : Bool) :
    Trace program (4 * bits.length + 6)
      (cfg (some 2) value present (true :: (Encoding.frame bits ++ rest)) output)
      (cfg (some 2) false true rest (true :: output)) := by
  have h := (begin_record value present (Encoding.frame bits ++ rest) output).trans
    (frame_trace bits rest (true :: output) true true)
  convert h using 1 ; omega

theorem finish (value present : Bool) (rest output : List Bool) :
    Trace program 5 (cfg (some 2) value present (false :: rest) output)
      (cfg none false false rest output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

def loopSteps (records : List (List Bool)) : ℕ :=
  4 * (records.map List.length).sum + 6 * records.length + 5

theorem loop_trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (loopSteps records)
      (cfg (some 2) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (List.replicate records.length true ++ output)) := by
  induction records generalizing value present output with
  | nil => simpa [loopSteps, Encoding.encodeList] using finish value present suffix output
  | cons bits records ih =>
      have h := (record_trace bits (Encoding.encodeList id records ++ suffix) output
        value present).trans (ih (true :: output) false true)
      have hout : List.replicate records.length true ++ true :: output =
          List.replicate (records.length + 1) true ++ output := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [hout] at h
      convert h using 1 <;>
        simp [loopSteps, Encoding.encodeList, Nat.mul_add, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm, List.append_assoc]

def steps (records : List (List Bool)) : ℕ := loopSteps records + 2

theorem trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (steps records)
      (cfg (some program.entry) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (Encoding.encodeNat records.length ++ output)) := by
  have h := (start value present (Encoding.encodeList id records ++ suffix) output).trans
    (loop_trace records suffix (false :: output) false present)
  simpa [steps, Encoding.encodeNat, Nat.add_comm, List.append_assoc] using h

theorem steps_le_encoded (records : List (List Bool)) :
    steps records ≤ 3 * (Encoding.encodeList id records).length + 4 := by
  have hlen := ProgramEncoding.encodeRecords_length records
  change (Encoding.encodeList id records).length = _ at hlen
  unfold steps loopSteps
  omega

/-- Canonical-input/canonical-output execution, with no residual work data. -/
theorem complete_trace (records : List (List Bool)) :
    Trace program (steps records)
      (initial program (Encoding.encodeList id records))
      (terminal program (Encoding.encodeNat records.length)) := by
  have h := trace records [] [] false false
  convert h using 1
  · simp only [initial, cfg, List.append_nil, Cfg.mk.injEq, true_and]
    constructor <;> funext i <;> fin_cases i <;> rfl
  · simp only [terminal, cfg, List.append_nil, Cfg.mk.injEq, true_and]
    constructor <;> funext i <;> fin_cases i <;> rfl

/-- The existing compiler transfers this actual finite program to primitive tape steps. -/
theorem primitive_execution (records : List (List Bool)) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (3 * (Encoding.encodeList id records).length + 4))
      (primitiveCfg program (initial program (Encoding.encodeList id records)))
      (primitiveCfg program (terminal program (Encoding.encodeNat records.length))) := by
  exact BitProgram.primitive_execution program ⟨steps records, steps_le_encoded records, complete_trace records⟩

end CountRecords

namespace Intersection

open StructuredCalls
open ExecCNFSubset

/-- Membership with a preserved query and fully cleared work ports. -/
abbrev probe : Cmd 10 8 :=
  .seq copyTarget (.seq memberCall (.seq (clear 3) (clear 4)))

theorem probe_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hquery : d.stacks 1 = query.reverse) (valid : invariant records d) :
    ∃ n ≤ perRecordCost records query, ∃ e : Data,
      Eval probe n d e ∧ invariant records e ∧
      e.regs 4 = decide (query ∈ records) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = query.reverse ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
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
  let result := cleared 4 (cleared 3 e)
  let steps := (7 * (d.stacks 2).length + 5) +
    (n + ((2 * (e.stacks 3).length + 3) + (2 * (e.stacks 4).length + 3)))
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps, perRecordCost]
    rw [htarget, hp]
    simp only [List.length_cons, List.length_nil]
    nlinarith
  · apply Eval.seq (copyTarget_eval d hcopyTemp)
    apply Eval.seq he
    apply Eval.seq (clear_eval 3 e)
    simpa [cleared, StackRoutines.clearStacks] using clear_eval 4 (cleared 3 e)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [result, cleared, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, htarget] using htwo
    · simp [result, StackRoutines.clearStacks]
    · simp [result, StackRoutines.clearStacks]
    · simpa [result, cleared, StackRoutines.clearStacks] using hc
    · simpa [result, cleared, StackRoutines.clearStacks] using ht
    · simpa [result, cleared, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, hcopyTemp] using hseven
  · simpa [result, cleared, readRegs] using ha
  · simpa [result, cleared, StackRoutines.clearStacks, copied,
      StackRoutines.copyStacks] using hzero
  · simpa [result, cleared, StackRoutines.clearStacks] using hq
  · simpa [result, cleared, readRegs, copied] using hr7
  · simpa [result, cleared, readRegs, copied] using hr8
  · simpa [result, cleared, readRegs, copied] using hr9

/-- A concrete fixed-table subroutine, ready to be relocated into a caller. -/
def probeProgram := compiled probe 1 1

theorem probe_trace (query : List Bool) (records : List (List Bool)) (d : Data)
    (hquery : d.stacks 1 = query.reverse) (valid : invariant records d) :
    ∃ n ≤ perRecordCost records query + 1, ∃ e : Data,
      Trace probeProgram n (d.withPC (some probeProgram.entry)) (e.withPC none) ∧
      invariant records e ∧ e.regs 4 = decide (query ∈ records) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = query.reverse ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  obtain ⟨n, hn, e, he, hi, h4, h0, h1, h7, h8, h9⟩ := probe_eval query records d hquery valid
  exact ⟨n + 1, by omega, e, compiled_halt_trace he 1 1, hi, h4, h0, h1, h7, h8, h9⟩


/-- The probe changes no stack at all when called with clean workspace. -/
theorem probe_preserving (query : List Bool) (records : List (List Bool)) (d : Data)
    (hquery : d.stacks 1 = query.reverse) (valid : invariant records d) :
    ∃ n ≤ perRecordCost records query + 1, ∃ e : Data,
      Trace probeProgram n (d.withPC (some probeProgram.entry)) (e.withPC none) ∧
      e.stacks = d.stacks ∧ e.regs 4 = decide (query ∈ records) ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 := by
  obtain ⟨n, hn, e, he, hi, h4, h0, h1, h7, h8, h9⟩ := probe_trace query records d hquery valid
  refine ⟨n, hn, e, he, ?_, h4, h7, h8, h9⟩
  rcases valid with ⟨d2, d3, d4, d5, d6, d7⟩
  rcases hi with ⟨e2, e3, e4, e5, e6, e7⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1.trans hquery.symm
  · exact e2.trans d2.symm
  · exact e3.trans d3.symm
  · exact e4.trans d4.symm
  · exact e5.trans d5.symm
  · exact e6.trans d6.symm
  · exact e7.trans d7.symm

abbrev Caller := State 11 9

def probeReg (i : Fin 10) : Fin 11 := i.castSucc

def targetPort (second : Bool) : Fin 9 := if second then 8 else 2

def probeStack (second : Bool) (i : Fin 8) : Fin 9 :=
  if i = 2 then targetPort second else i.castSucc

theorem probeReg_injective : Function.Injective probeReg := Fin.castSucc_injective 10

theorem probeStack_injective (second : Bool) : Function.Injective (probeStack second) := by
  cases second <;> intro i j h <;> fin_cases i <;> fin_cases j <;>
    simp_all [probeStack, targetPort]

abbrev probeCall (second : Bool) : Cmd 11 9 :=
  .call (ProgramLinking.liftProgram probeProgram probeReg (probeStack second))

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

/-- Workspace is independent of the two preserved target clauses. -/
def Clean (d : Caller) : Prop :=
  d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧
    d.stacks 6 = [] ∧ d.stacks 7 = []

/-- The same fixed probe code is relocated to either target clause, with an
extra untouched register available for the first Boolean answer. -/
theorem probeCall_eval (second : Bool) (query : List Bool)
    (records : List (List Bool)) (d : Caller)
    (hquery : d.stacks 1 = query.reverse)
    (htarget : d.stacks (targetPort second) = Encoding.encodeList id records)
    (hclean : Clean d) :
    ∃ n ≤ perRecordCost records query + 1, ∃ e : Caller,
      Eval (probeCall second) n d e ∧ e.stacks = d.stacks ∧
      e.regs 4 = decide (query ∈ records) ∧ e.regs 7 = d.regs 7 ∧
      e.regs 8 = d.regs 8 ∧ e.regs 9 = d.regs 9 ∧ e.regs 10 = d.regs 10 := by
  let a : Data := ⟨d.regs ∘ probeReg, d.stacks ∘ probeStack second⟩
  have haq : a.stacks 1 = query.reverse := by simpa [a, probeStack] using hquery
  have hav : invariant records a := by
    rcases hclean with ⟨h3, h4, h5, h6, h7⟩
    exact ⟨by simpa [a, probeStack] using htarget,
      by simpa [a, probeStack] using h3, by simpa [a, probeStack] using h4,
      by simpa [a, probeStack] using h5, by simpa [a, probeStack] using h6,
      by simpa [a, probeStack] using h7⟩
  obtain ⟨n, hn, b, ht, hs, h4, h7, h8, h9⟩ := probe_preserving query records a haq hav
  have heval := eval_call_lifted probeProgram probeReg (probeStack second) d
    probeReg_injective (probeStack_injective second) ht
  have hea : embedState probeReg (probeStack second) d a = d :=
    embed_restricted _ _ probeReg_injective (probeStack_injective second) d
  rw [hea] at heval
  let e := embedState probeReg (probeStack second) d b
  have hstack (i : Fin 8) : e.stacks (probeStack second i) = b.stacks i :=
    embedState_stack _ _ _ _ (probeStack_injective second) i
  have hreg (i : Fin 10) : e.regs (probeReg i) = b.regs i :=
    embedState_register _ _ _ _ probeReg_injective i
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    by_cases hm : ∃ j, probeStack second j = i
    · obtain ⟨j, rfl⟩ := hm
      rw [hstack, hs]
      rfl
    · exact embedState_stack_frame _ _ _ _ _ hm
  · exact (hreg 4).trans h4
  · exact (hreg 7).trans h7
  · exact (hreg 8).trans h8
  · exact (hreg 9).trans h9
  · exact embedState_register_frame _ _ _ _ _ (by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have := j.isLt
      simp [probeReg] at hv
      omega)


def saved (d : Caller) : Caller := ⟨Function.update d.regs 10 (d.regs 4), d.stacks⟩
abbrev saveAnswer : Cmd 11 9 := .base (.atom (.copy 10 4))

theorem saveAnswer_eval (d : Caller) : Eval saveAnswer 1 d (saved d) := by
  change Eval (.base (.atom (.copy 10 4))) 1 d ((StructuredProgram.Atom.copy 10 4).eval d)
  exact .base (.atom _ _)

def marked (d : Caller) : Caller :=
  ⟨Function.update d.regs 9 (d.regs 10 && !(d.regs 4)), d.stacks⟩

abbrev markViolation : Cmd 11 9 :=
  .seq (.base (.atom (.bnot 9 4))) (.base (.atom (.band 9 10 9)))

theorem markViolation_eval (d : Caller) : Eval markViolation 2 d (marked d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.bnot 9 4) d))
    (Eval.base (StructuredProgram.Eval.atom (.band 9 10 9)
      ((StructuredProgram.Atom.bnot 9 4).eval d)))
  simpa [markViolation, marked, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

abbrev clearQueryProgram : Program 11 9 3 := StackRoutines.clearProgram 1 0 1

def clearedQuery (d : Caller) : Caller :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 1 d.stacks⟩

abbrev clearQuery : Cmd 11 9 := .call clearQueryProgram

theorem clearQuery_eval (d : Caller) :
    Eval clearQuery (2 * (d.stacks 1).length + 3) d (clearedQuery d) := by
  have h := StackRoutines.clearProgram_trace (r := 11) (s := 9) 1 0 1 d.regs d.stacks
  have hh : step clearQueryProgram (StackRoutines.clearResult 2 1 0 1 d.regs d.stacks) =
      some ((clearedQuery d).withPC none) := by
    simp [step, StackRoutines.clearResult,
      clearedQuery, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [clearQueryProgram, clearedQuery, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

/-- A real callback for the violation q∈D and q∉H. Both target encodings are
preserved; the reversed query payload is consumed after both probes finish. -/
abbrev callback : Cmd 11 9 :=
  .seq (probeCall false) (.seq saveAnswer
    (.seq (probeCall true) (.seq markViolation clearQuery)))

def violation (D H : List (List Bool)) (query : List Bool) : Bool :=
  decide (query ∈ D) && !decide (query ∈ H)

def comparisonCost (D H : List (List Bool)) (query : List Bool) : ℕ :=
  120 * (query.length + 1) *
    ((Encoding.encodeList id D).length + (Encoding.encodeList id H).length + 2)

theorem callback_eval (query : List Bool) (D H : List (List Bool)) (d : Caller)
    (hquery : d.stacks 1 = query.reverse)
    (hD : d.stacks 2 = Encoding.encodeList id D)
    (hH : d.stacks 8 = Encoding.encodeList id H) (hclean : Clean d) :
    ∃ n ≤ comparisonCost D H query, ∃ e : Caller,
      Eval callback n d e ∧ e.regs 9 = violation D H query ∧
      e.stacks = Function.update d.stacks 1 [] ∧
      e.regs 7 = d.regs 7 ∧ e.regs 8 = d.regs 8 := by
  obtain ⟨nD, hnD, eD, heD, hsD, haD, h7D, h8D, h9D, h10D⟩ :=
    probeCall_eval false query D d hquery hD hclean
  have hq' : (saved eD).stacks 1 = query.reverse := by simpa [saved, hsD] using hquery
  have hH' : (saved eD).stacks 8 = Encoding.encodeList id H := by
    simpa [saved, hsD] using hH
  have hclean' : Clean (saved eD) := by simpa [Clean, saved, hsD] using hclean
  obtain ⟨nH, hnH, eH, heH, hsH, haH, h7H, h8H, h9H, h10H⟩ :=
    probeCall_eval true query H (saved eD) hq' hH' hclean'
  let result := clearedQuery (marked eH)
  let steps := nD + (1 + (nH + (2 + (2 * (eH.stacks 1).length + 3))))
  have hs : eH.stacks = d.stacks := by simpa [saved, hsD] using hsH
  have hlen : (eH.stacks 1).length = query.length := by rw [hs, hquery, List.length_reverse]
  refine ⟨steps, ?_, result, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [steps, comparisonCost]
    rw [hlen]
    dsimp [ExecCNFSubset.perRecordCost] at hnD hnH
    nlinarith only [hnD, hnH]
  · apply Eval.seq heD
    apply Eval.seq (saveAnswer_eval eD)
    apply Eval.seq heH
    apply Eval.seq (markViolation_eval eH)
    exact clearQuery_eval (marked eH)
  · have h10 : eH.regs 10 = decide (query ∈ D) := by
      simpa [saved, haD] using h10H
    simp [result, clearedQuery, marked, readRegs, violation, h10, haH]
  · simp [result, clearedQuery, marked, StackRoutines.clearStacks, hs]
  · simpa [result, clearedQuery, marked, readRegs, saved, h7D] using h7H
  · simpa [result, clearedQuery, marked, readRegs, saved, h8D] using h8H

/-- The source iterator needs only these two persistent target encodings. -/
def targets (D H : List (List Bool)) (d : Caller) : Prop :=
  d.stacks 2 = Encoding.encodeList id D ∧ d.stacks 8 = Encoding.encodeList id H ∧ Clean d

def ports : RecordPrograms.Ports 11 9 where
  tag := 7
  present := 8
  found := 9
  source := 0
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem callback_contract (D H : List (List Bool)) :
    RecordPrograms.CallbackContract ports callback (violation D H)
      (comparisonCost D H) (targets D H) := by
  intro query tail base hbase
  let d := RecordPrograms.state ports base false true false tail query.reverse
  have hq : d.stacks 1 = query.reverse := by simp [d, RecordPrograms.state, ports]
  have hd : targets D H d := by simpa [targets, Clean, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, ha, hs, h7, h8⟩ := callback_eval query D H d hq hd.1 hd.2.1 hd.2.2
  have htargets : targets D H e := by
    simpa [targets, Clean, hs] using hd
  have heState : RecordPrograms.state ports e false true (violation D H query) tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using h7
    · simpa [d, RecordPrograms.state, ports] using h8
    · exact ha
    · simp [hs, d, RecordPrograms.state, ports]
    · simp [hs, ports]
  refine ⟨n, e, hn, htargets, ?_⟩
  rw [heState]
  exact he


/-- Semantic property checked by the concrete two-membership scan. -/
def ContainsIntersection (C D H : List (List Bool)) : Prop :=
  ∀ q ∈ C, q ∈ D → q ∈ H

theorem no_violation_iff (C D H : List (List Bool)) :
    C.any (violation D H) = false ↔ ContainsIntersection C D H := by
  simp [List.any_eq_false, violation, ContainsIntersection]

abbrev emitAnswer : Cmd 11 9 :=
  .seq (.base (.atom (.bnot 9 9))) (.base (.atom (.push 1 9)))

def answered (d : Caller) : Caller :=
  ⟨Function.update d.regs 9 (!(d.regs 9)),
    Function.update d.stacks 1 ((!(d.regs 9)) :: d.stacks 1)⟩

theorem emitAnswer_eval (d : Caller) : Eval emitAnswer 2 d (answered d) := by
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom (.bnot 9 9) d))
    (Eval.base (StructuredProgram.Eval.atom (.push 1 9)
      ((StructuredProgram.Atom.bnot 9 9).eval d)))
  simpa [emitAnswer, answered, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

/-- Test `C ∩ D ⊆ H`. All three encoded clauses live on stacks, independent
of the fixed finite instruction table. C is consumed; D and H are preserved. -/
abbrev command : Cmd 11 9 :=
  .seq (RecordPrograms.iterate ports callback) emitAnswer

def runBound (C D H : List (List Bool)) : ℕ :=
  (240 * ((Encoding.encodeList id D).length + (Encoding.encodeList id H).length + 2) + 20) *
    ((Encoding.encodeList id C).length + 1)

theorem command_eval (C D H : List (List Bool)) (suffix : List Bool)
    (base : Caller) (valid : targets D H base) (v pr f : Bool) :
    ∃ n ≤ runBound C D H, ∃ next : Caller, targets D H next ∧
      Eval command n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList id C ++ suffix) [])
        (RecordPrograms.state ports next false true (!(C.any (violation D H)))
          (RecordPrograms.unread (violation D H) C suffix)
          [!(C.any (violation D H))]) := by
  obtain ⟨n, next, hn, hnext, he⟩ := RecordPrograms.iterate_run ports callback
    (violation D H) (comparisonCost D H) (targets D H) (callback_contract D H)
    C suffix base valid v pr f
  let done := RecordPrograms.state ports next false true (C.any (violation D H))
    (RecordPrograms.unread (violation D H) C suffix) []
  have hfinal : answered done =
      RecordPrograms.state ports next false true (!(C.any (violation D H)))
        (RecordPrograms.unread (violation D H) C suffix) [!(C.any (violation D H))] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ done, RecordPrograms.state, ports]
    · funext i
      fin_cases i <;> simp [ done, RecordPrograms.state, ports]
  have hb := RecordPrograms.program_budget_le_input (comparisonCost D H) C
    (120 * ((Encoding.encodeList id D).length + (Encoding.encodeList id H).length + 2))
    (120 * ((Encoding.encodeList id D).length + (Encoding.encodeList id H).length + 2)) (by
      intro bits hbits
      simp only [comparisonCost]
      nlinarith)
  refine ⟨n + 2, ?_, next, hnext, ?_⟩
  · change 4 + RecordPrograms.budget (comparisonCost D H) C ≤
      (_ + _ + 17) * ((Encoding.encodeList id C).length + 1) at hb
    unfold runBound
    nlinarith
  · have hfin := emitAnswer_eval done
    rw [hfinal] at hfin
    exact Eval.seq he hfin

/-- Fixed syntax compiles to one finite machine, not a family indexed by the
number or size of the runtime clauses. -/
def program := compiled command 0 1

theorem program_run (C D H : List (List Bool)) (suffix : List Bool)
    (base : Caller) (valid : targets D H base) (v pr f : Bool) :
    ∃ next : Caller, targets D H next ∧
      RunsIn program (runBound C D H + 1)
        ((RecordPrograms.state ports base v pr f (Encoding.encodeList id C ++ suffix) []).withPC
          (some program.entry))
        ((RecordPrograms.state ports next false true (!(C.any (violation D H)))
          (RecordPrograms.unread (violation D H) C suffix)
          [!(C.any (violation D H))]).withPC none) := by
  obtain ⟨n, hn, next, hi, he⟩ := command_eval C D H suffix base valid v pr f
  exact ⟨next, hi, n + 1, by omega, compiled_halt_trace he 0 1⟩

theorem primitive_run (C D H : List (List Bool)) (suffix : List Bool)
    (base : Caller) (valid : targets D H base) (v pr f : Bool) :
    ∃ next : Caller, targets D H next ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (runBound C D H + 1))
        (primitiveCfg program
          ((RecordPrograms.state ports base v pr f (Encoding.encodeList id C ++ suffix) []).withPC
            (some program.entry)))
        (primitiveCfg program
          ((RecordPrograms.state ports next false true (!(C.any (violation D H)))
            (RecordPrograms.unread (violation D H) C suffix)
            [!(C.any (violation D H))]).withPC none)) := by
  obtain ⟨next, hi, ht⟩ := program_run C D H suffix base valid v pr f
  exact ⟨next, hi, BitProgram.primitive_execution program ht⟩

theorem answer_correct (C D H : List (List Bool)) :
    (!(C.any (violation D H))) = true ↔ ContainsIntersection C D H := by
  simpa using no_violation_iff C D H

/-- A fixed input schema for the relational checker: two framed target clauses,
then the source clause. All clause and literal counts remain runtime data. -/
def rawInput (C D H : List (List Bool)) : List Bool :=
  Encoding.frame (Encoding.encodeList id D) ++
    Encoding.frame (Encoding.encodeList id H) ++ Encoding.encodeList id C

abbrev transferProgram (port : Fin 9) : Program 11 9 4 :=
  StackRoutines.transferProgram 1 port 0 1

abbrev transfer (port : Fin 9) : Cmd 11 9 := .call (transferProgram port)

def transferred (port : Fin 9) (d : Caller) : Caller :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 1 port d.stacks⟩

theorem transfer_eval (port : Fin 9) (hport : (1 : Fin 9) ≠ port) (d : Caller) :
    Eval (transfer port) (3 * (d.stacks 1).length + 3) d (transferred port d) := by
  have h := StackRoutines.transferProgram_trace (r := 11) (s := 9)
    1 port 0 1 hport (by decide) d.regs d.stacks
  have hh : step (transferProgram port)
      (StackRoutines.transferResult 3 1 port 0 1 d.regs d.stacks) =
      some ((transferred port d).withPC none) := by
    simp [step,
      StackRoutines.transferResult, transferred, StructuredProgram.State.withPC, execInstr]
  apply Eval.call
  simpa [transferProgram, transferred, StructuredProgram.State.withPC, Nat.add_assoc] using
    h.trans (.cons hh (.refl _))

def loadedD (C D H : List (List Bool)) : Caller :=
  RecordPrograms.state ports (StructuredProgram.ioState 0 []) false true false
    (Encoding.frame (Encoding.encodeList id H) ++ Encoding.encodeList id C)
    (Encoding.encodeList id D).reverse

def loadedH (C D H : List (List Bool)) : Caller :=
  RecordPrograms.state ports (transferred 2 (loadedD C D H)) false true false
    (Encoding.encodeList id C) (Encoding.encodeList id H).reverse

def ready (C D H : List (List Bool)) : Caller := transferred 8 (loadedH C D H)

theorem loadD_eval (C D H : List (List Bool)) :
    Eval (RecordPrograms.reader ports) (6 * (Encoding.encodeList id D).length + 4)
      (StructuredProgram.ioState 0 (rawInput C D H)) (loadedD C D H) := by
  have he := RecordPrograms.reader_eval ports (StructuredProgram.ioState 0 [])
    (Encoding.encodeList id D)
    (Encoding.frame (Encoding.encodeList id H) ++ Encoding.encodeList id C)
    [] false false false
  have hs : RecordPrograms.state ports (StructuredProgram.ioState 0 []) false false false
      (Encoding.frame (Encoding.encodeList id D) ++
        (Encoding.frame (Encoding.encodeList id H) ++ Encoding.encodeList id C)) [] =
      StructuredProgram.ioState 0 (rawInput C D H) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ ports ]
    · funext i
      fin_cases i <;> simp [ ports,
        rawInput, List.append_assoc]
  rw [hs] at he
  simpa only [loadedD, List.append_nil] using he

theorem loadH_eval (C D H : List (List Bool)) :
    Eval (RecordPrograms.reader ports) (6 * (Encoding.encodeList id H).length + 4)
      (transferred 2 (loadedD C D H)) (loadedH C D H) := by
  have he := RecordPrograms.reader_eval ports (transferred 2 (loadedD C D H))
    (Encoding.encodeList id H) (Encoding.encodeList id C) [] false true false
  have hs : RecordPrograms.state ports (transferred 2 (loadedD C D H))
      false true false
      (Encoding.frame (Encoding.encodeList id H) ++ Encoding.encodeList id C) [] =
      transferred 2 (loadedD C D H) := by
    apply RecordPrograms.state_eq_self <;>
      simp [transferred, loadedD, RecordPrograms.state, ports, readRegs,
        StackRoutines.transferStacks ]
  rw [hs] at he
  simpa only [loadedH, List.append_nil] using he

theorem ready_targets (C D H : List (List Bool)) : targets D H (ready C D H) := by
  simp [ready, loadedH, loadedD, transferred, targets, Clean, RecordPrograms.state,
    ports, StackRoutines.transferStacks ]

abbrev rawCommand : Cmd 11 9 :=
  .seq (RecordPrograms.reader ports) (.seq (transfer 2)
    (.seq (RecordPrograms.reader ports) (.seq (transfer 8) command)))

def rawProgram := compiled rawCommand 0 1

theorem rawCommand_eval (C D H : List (List Bool)) :
    ∃ n ≤ 1024 * ((rawInput C D H).length + 1)^2, ∃ e : Caller,
      Eval rawCommand n (StructuredProgram.ioState 0 (rawInput C D H)) e ∧
      e.stacks 1 = [!(C.any (violation D H))] ∧ targets D H e := by
  obtain ⟨n, hn, next, hnxt, he⟩ := command_eval C D H [] (ready C D H)
    (ready_targets C D H) false true false
  have hs : RecordPrograms.state ports (ready C D H) false true false
      (Encoding.encodeList id C ++ []) [] = ready C D H := by
    apply RecordPrograms.state_eq_self <;>
      simp [ready, loadedH, loadedD, transferred, RecordPrograms.state, ports,
        StackRoutines.transferStacks, readRegs ]
  rw [hs] at he
  let e := RecordPrograms.state ports next false true (!(C.any (violation D H)))
    (RecordPrograms.unread (violation D H) C []) [!(C.any (violation D H))]
  refine ⟨(6 * (Encoding.encodeList id D).length + 4) +
    ((3 * ((loadedD C D H).stacks 1).length + 3) +
      ((6 * (Encoding.encodeList id H).length + 4) +
        ((3 * ((loadedH C D H).stacks 1).length + 3) + n))), ?_, e, ?_, ?_, ?_⟩
  · have hd : ((loadedD C D H).stacks 1).length = (Encoding.encodeList id D).length := by
      simp [loadedD, RecordPrograms.state, ports]
    have hh : ((loadedH C D H).stacks 1).length = (Encoding.encodeList id H).length := by
      simp [loadedH, RecordPrograms.state, ports]
    rw [hd, hh]
    unfold runBound at hn
    simp only [rawInput, List.length_append, Encoding.length_frame]
    nlinarith [sq_nonneg ((Encoding.encodeList id C).length : ℤ),
      sq_nonneg ((Encoding.encodeList id D).length : ℤ),
      sq_nonneg ((Encoding.encodeList id H).length : ℤ)]
  · exact Eval.seq (loadD_eval C D H) (Eval.seq (transfer_eval 2 (by decide) _)
      (Eval.seq (loadH_eval C D H) (Eval.seq (transfer_eval 8 (by decide) _) he)))
  · simp [e, RecordPrograms.state, ports]
  · simpa [e, targets, Clean, RecordPrograms.state, ports] using hnxt

theorem rawProgram_runsIn (C D H : List (List Bool)) :
    ∃ e : Caller, e.stacks 1 = [!(C.any (violation D H))] ∧
      RunsIn rawProgram (1024 * ((rawInput C D H).length + 1)^2 + 1)
        (initial rawProgram (rawInput C D H)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hout, _⟩ := rawCommand_eval C D H
  exact ⟨e, hout, n + 1, by omega, compiled_halt_trace he 0 1⟩

theorem rawProgram_primitive_outputs (C D H : List (List Bool)) :
    ∃ e : Caller, e.stacks 1 = [!(C.any (violation D H))] ∧
      Computation.RunsIn (primitive rawProgram).step
        (primitiveOverhead rawProgram * (1024 * ((rawInput C D H).length + 1)^2 + 1))
        (primitiveCfg rawProgram (initial rawProgram (rawInput C D H)))
        (primitiveCfg rawProgram (e.withPC none)) := by
  obtain ⟨e, he, ht⟩ := rawProgram_runsIn C D H
  exact ⟨e, he, BitProgram.primitive_execution rawProgram ht⟩

end Intersection
end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
