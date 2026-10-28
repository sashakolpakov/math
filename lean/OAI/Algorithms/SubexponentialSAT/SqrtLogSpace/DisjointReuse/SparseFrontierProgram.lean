import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.ExecWorklistProgram

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

abbrev state := SubexpNormalizeProgram.filterState

def transfer (src dst : Fin 4) : Cmd 3 4 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 3) 1)

theorem transfer_eval (src dst : Fin 4) (hsd : src ≠ dst) (d : State 3 4) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩ := by
  exact Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide)
    d.regs d.stacks)

/-- Consume the current forward body and prepend its escaped record. -/
def push : Cmd 3 4 :=
  .seq (transfer 0 3) (.call SubexpNormalizeProgram.emitRecordProgram)

theorem push_eval (body saved pending : List Bool) (v p flag : Bool) :
    Eval push (8 * body.length + 10)
      (state v p flag body saved pending [])
      (state true false flag [] saved (true :: (Encoding.frame body ++ pending)) []) := by
  have ht : Eval (transfer 0 3) (3 * body.length + 3)
      (state v p flag body saved pending [])
      (state false false flag [] saved pending body.reverse) := by
    simpa [state, SubexpNormalizeProgram.filterState, StackRoutines.transferStacks,
      readRegs] using transfer_eval 0 3 (by decide)
        (state v p flag body saved pending [])
  have he := Eval.call _
    (SubexpNormalizeProgram.emitRecord_trace body [] saved pending false false flag)
  convert ht.seq he using 1 <;> first | rfl | omega

/-- Initialize the one-root frontier with its physical empty-list sentinel. -/
def initFrontier : Cmd 3 4 :=
  .seq (.base (.seq (.atom (.set 0 false)) (.atom (.push 2 0)))) push

theorem initFrontier_eval (body saved : List Bool) (v p flag : Bool) :
    Eval initFrontier (8 * body.length + 12)
      (state v p flag body saved [] [])
      (state true false flag [] saved (Encoding.encodeList id [body]) []) := by
  have hs : Eval (.base (.seq (.atom (.set (0 : Fin 3) false))
      (.atom (.push (2 : Fin 4) 0)))) 2
      (state v p flag body saved [] []) (state false p flag body saved [false] []) := by
    have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false)
      (state v p flag body saved [] [])).seq
        (StructuredProgram.Eval.atom (.push (2 : Fin 4) (0 : Fin 3)) _)
    simpa [state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC,
      StructuredProgram.State.ofCfg, execInstr] using Eval.base h
  have hp := push_eval body saved [false] false p flag
  have h := hs.seq hp
  change Eval initFrontier (2 + (8 * body.length + 10)) _ _ at h
  convert h using 1
  · ring
  · simp [Encoding.encodeList]

def readerPorts : RecordPrograms.Ports 3 4 :=
  ⟨0, 1, 2, 2, 3, by decide, by decide, by decide, by decide⟩

theorem reader_state (base : State 3 4) (current saved source payload : List Bool)
    (v p flag : Bool)
    (h0 : base.stacks 0 = current) (h1 : base.stacks 1 = saved) :
    RecordPrograms.state readerPorts base v p flag source payload =
      state v p flag current saved source payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [readerPorts, triple]
  · funext i
    fin_cases i <;> simp [readerPorts, quadruple, h0, h1]

/-- The head is known to exist: remove its list tag, parse its frame, then
restore forward order on the empty current-body port. -/
def pop : Cmd 3 4 :=
  .seq (.base (.atom (.pop 2 0 1)))
    (.seq (RecordPrograms.reader readerPorts) (transfer 3 0))

theorem pop_eval (body saved pending : List Bool) (v p flag : Bool) :
    Eval pop (9 * body.length + 8)
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false flag body saved pending []) := by
  have hp : Eval (.base (.atom (.pop (2 : Fin 4) (0 : Fin 3) 1))) 1
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state true true flag [] saved (Encoding.frame body ++ pending) []) := by
    simpa [state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, readRegs]
      using Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) (0 : Fin 3) 1)
        (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []))
  let base := state true true flag [] saved (Encoding.frame body ++ pending) []
  have hr : Eval (RecordPrograms.reader readerPorts) (6 * body.length + 4)
      base (state false true flag [] saved pending body.reverse) := by
    have h := RecordPrograms.reader_eval readerPorts base body pending [] true true flag
    rw [reader_state base [] saved _ _ _ _ _ rfl rfl,
      reader_state base [] saved _ _ _ _ _ rfl rfl] at h
    simpa [base] using h
  have ht : Eval (transfer 3 0) (3 * body.length + 3)
      (state false true flag [] saved pending body.reverse)
      (state false false flag body saved pending []) := by
    simpa [state, SubexpNormalizeProgram.filterState, StackRoutines.transferStacks,
      readRegs] using transfer_eval 3 0 (by decide)
        (state false true flag [] saved pending body.reverse)
  convert hp.seq (hr.seq ht) using 1 <;> first | rfl | omega

/-- The test preserves every stack, including the empty-list sentinel. -/
def test : Cmd 3 4 := .base (.atom (.peek 2 2 1))

theorem test_eval (b : Bool) (tail current saved scratch : List Bool) (v p flag : Bool) :
    Eval test 1 (state v p flag current saved (b :: tail) scratch)
      (state v true b current saved (b :: tail) scratch) := by
  simpa [test, state, SubexpNormalizeProgram.filterState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr, readRegs]
    using Eval.base (StructuredProgram.Eval.atom (.peek (2 : Fin 4) (2 : Fin 3) 1)
      (state v p flag current saved (b :: tail) scratch))

/-- A public pop operation tests the sentinel itself. Empty work is a no-op
on every stack, rather than a removal of the final delimiter. -/
def popIfPresent : Cmd 3 4 := .seq test (.ite 2 pop (.base .skip))

theorem popIfPresent_empty (saved : List Bool) (v p flag : Bool) :
    Eval popIfPresent 2 (state v p flag [] saved [false] [])
      (state v true false [] saved [false] []) := by
  have ht := test_eval false [] [] saved [] v p flag
  have hs : Eval (.ite (2 : Fin 3) pop (.base .skip)) 1
      (state v true false [] saved [false] []) (state v true false [] saved [false] []) :=
    .ite_false rfl (.base (.skip _))
  exact ht.seq hs

theorem popIfPresent_cons (body saved pending : List Bool) (v p flag : Bool) :
    Eval popIfPresent (9 * body.length + 10)
      (state v p flag [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false true body saved pending []) := by
  have ht := test_eval true (Encoding.frame body ++ pending) [] saved [] v p flag
  have hp : Eval (.ite (2 : Fin 3) pop (.base .skip)) (9 * body.length + 9)
      (state v true true [] saved (true :: (Encoding.frame body ++ pending)) [])
      (state false false true body saved pending []) := by
    simpa only [Nat.add_assoc] using
      Eval.ite_true (no := .base .skip) (test := (2 : Fin 3)) rfl
        (pop_eval body saved pending v true true)
  convert ht.seq hp using 1 <;> first | rfl | omega

def pushProgram : Program 3 4 (size push + 1) := compiled push 0 2

def initFrontierProgram : Program 3 4 (size initFrontier + 1) := compiled initFrontier 0 2

theorem initFrontier_trace (body saved : List Bool) (v p flag : Bool) :
    Trace initFrontierProgram (8 * body.length + 13)
      ((state v p flag body saved [] []).withPC (some initFrontierProgram.entry))
      ((state true false flag [] saved (Encoding.encodeList id [body]) []).withPC none) := by
  simpa only [initFrontierProgram, Nat.add_assoc] using compiled_halt_trace
    (initFrontier_eval body saved v p flag) 0 2

def popProgram : Program 3 4 (size pop + 1) := compiled pop 2 0

def popIfPresentProgram : Program 3 4 (size popIfPresent + 1) := compiled popIfPresent 2 0

theorem popIfPresent_empty_trace (saved : List Bool) (v p flag : Bool) :
    Trace popIfPresentProgram 3
      ((state v p flag [] saved [false] []).withPC (some popIfPresentProgram.entry))
      ((state v true false [] saved [false] []).withPC none) :=
  compiled_halt_trace (popIfPresent_empty saved v p flag) 2 0

theorem popIfPresent_cons_trace (body saved pending : List Bool) (v p flag : Bool) :
    Trace popIfPresentProgram (9 * body.length + 11)
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popIfPresentProgram.entry))
      ((state false false true body saved pending []).withPC none) := by
  simpa only [popIfPresentProgram, Nat.add_assoc] using compiled_halt_trace
    (popIfPresent_cons body saved pending v p flag) 2 0

theorem push_trace (body saved pending : List Bool) (v p flag : Bool) :
    Trace pushProgram (8 * body.length + 11)
      ((state v p flag body saved pending []).withPC (some pushProgram.entry))
      ((state true false flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC none) := by
  simpa only [pushProgram, Nat.add_assoc] using compiled_halt_trace
    (push_eval body saved pending v p flag) 0 2

theorem pop_trace (body saved pending : List Bool) (v p flag : Bool) :
    Trace popProgram (9 * body.length + 9)
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popProgram.entry))
      ((state false false flag body saved pending []).withPC none) := by
  simpa only [popProgram, Nat.add_assoc] using compiled_halt_trace
    (pop_eval body saved pending v p flag) 2 0

theorem state_dataBits {l : ℕ} (pc : Option (Fin l))
    (current saved pending scratch : List Bool) (v p flag : Bool) :
    dataBits ((state v p flag current saved pending scratch).withPC pc) =
      current.length + saved.length + pending.length + scratch.length := by
  simp [dataBits, stackBits, state, SubexpNormalizeProgram.filterState,
    quadruple, Fin.sum_univ_succ, Nat.add_assoc]

/-- A local linear-time push cannot allocate more than a linear amount of
temporary data. The saved declared-n word is included explicitly. -/
theorem push_prefix_space (body saved pending : List Bool) (v p flag : Bool)
    (t : ℕ) (c : Cfg 3 4 (size push + 1)) (ht : t ≤ 8 * body.length + 11)
    (hc : Trace pushProgram t
      ((state v p flag body saved pending []).withPC (some pushProgram.entry)) c) :
    dataBits c ≤ saved.length + pending.length + 9 * body.length + 11 := by
  have h := trace_dataBits pushProgram hc
  rw [state_dataBits] at h
  simp only [List.length_nil] at h
  omega

theorem initFrontier_prefix_space (body saved : List Bool) (v p flag : Bool)
    (t : ℕ) (c : Cfg 3 4 (size initFrontier + 1)) (ht : t ≤ 8 * body.length + 13)
    (hc : Trace initFrontierProgram t
      ((state v p flag body saved [] []).withPC (some initFrontierProgram.entry)) c) :
    dataBits c ≤ saved.length + 9 * body.length + 13 := by
  have h := trace_dataBits initFrontierProgram hc
  rw [state_dataBits] at h
  simp only [List.length_nil] at h
  omega

theorem pop_prefix_space (body saved pending : List Bool) (v p flag : Bool)
    (t : ℕ) (c : Cfg 3 4 (size pop + 1)) (ht : t ≤ 9 * body.length + 9)
    (hc : Trace popProgram t
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popProgram.entry)) c) :
    dataBits c ≤ saved.length + pending.length + 11 * body.length + 11 := by
  have h := trace_dataBits popProgram hc
  rw [state_dataBits] at h
  simp only [List.length_nil, List.length_cons, List.length_append,
    Encoding.length_frame] at h
  omega

theorem popIfPresent_prefix_space (body saved pending : List Bool) (v p flag : Bool)
    (t : ℕ) (c : Cfg 3 4 (size popIfPresent + 1)) (ht : t ≤ 9 * body.length + 11)
    (hc : Trace popIfPresentProgram t
      ((state v p flag [] saved (true :: (Encoding.frame body ++ pending)) []).withPC
        (some popIfPresentProgram.entry)) c) :
    dataBits c ≤ saved.length + pending.length + 11 * body.length + 13 := by
  have h := trace_dataBits popIfPresentProgram hc
  rw [state_dataBits] at h
  simp only [List.length_nil, List.length_cons, List.length_append,
    Encoding.length_frame] at h
  omega

/-- The splitter may already return framed children. This fixed command
consumes B then A and never touches the saved declared-variable word. -/
def pushPair : Cmd 4 5 :=
  .seq (.call (ExecWorklistProgram.copyAt 3 0))
    (.call (ExecWorklistProgram.copyAt 2 0))

theorem pushPair_eval (left right saved pending : List Bool) (terminal v p flag : Bool) :
    Eval pushPair (13 * right.length + 13 * left.length + 36)
      (ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right))
      (ExecWorklistProgram.data terminal false false flag
        (ExecWorklistProgram.record left ++ (ExecWorklistProgram.record right ++ pending))
        saved [] []) := by
  have hb := ExecWorklistProgram.copyAt_eval 3 0 (by decide) (by decide) (by decide)
    (ExecWorklistProgram.data terminal v p flag pending saved
      (ExecWorklistProgram.record left ++ []) (ExecWorklistProgram.record right ++ []))
    right [] rfl rfl
  have ha := ExecWorklistProgram.copyAt_eval 2 0 (by decide) (by decide) (by decide)
    (ExecWorklistProgram.data terminal false false flag
      (ExecWorklistProgram.record right ++ pending) saved (ExecWorklistProgram.record left ++ []) [])
    left [] rfl rfl
  rw [ExecWorklistProgram.copyAfter_right] at hb
  rw [ExecWorklistProgram.copyAfter_left] at ha
  have h := hb.seq ha
  simp only [List.append_nil] at h
  convert h using 1 <;> first | rfl | omega

def pushPairProgram : Program 4 5 (size pushPair + 1) := compiled pushPair 2 0

theorem pushPair_trace (left right saved pending : List Bool) (terminal v p flag : Bool) :
    Trace pushPairProgram (13 * right.length + 13 * left.length + 37)
      ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry))
      ((ExecWorklistProgram.data terminal false false flag
        (ExecWorklistProgram.record left ++ (ExecWorklistProgram.record right ++ pending))
        saved [] []).withPC none) := by
  simpa only [pushPairProgram, Nat.add_assoc] using compiled_halt_trace
    (pushPair_eval left right saved pending terminal v p flag) 2 0

theorem pushPair_prefix_space (left right saved pending : List Bool) (terminal v p flag : Bool)
    (t : ℕ) (c : Cfg 4 5 (size pushPair + 1))
    (ht : t ≤ 13 * right.length + 13 * left.length + 37)
    (hc : Trace pushPairProgram t
      ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry)) c) :
    dataBits c ≤ pending.length + saved.length + 15 * (left.length + right.length) + 41 := by
  have h := trace_dataBits pushPairProgram hc
  have hstart : dataBits ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry)) =
      pending.length + saved.length + 2 * left.length + 2 * right.length + 4 := by
    simp [dataBits, stackBits, Fin.sum_univ_succ,
      ExecWorklistProgram.record_length, Nat.add_assoc]
    omega
  rw [hstart] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
