import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram

namespace OAI.Algorithms

/-! Actual framed-stream operations for the paired clause-family map. -/

namespace SubexponentialSAT.SubexpClauseFamilySupport

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 14 35

inductive Stream where
  | tables
  | scopes
  deriving DecidableEq

abbrev Stream.port : Stream → Fin 35
  | .tables => 32
  | .scopes => 33

abbrev transfer (src dst : Fin 35) : Cmd 14 35 := .call (transferProgram src dst 0 1)
def transferred (src dst : Fin 35) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 35) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

abbrev clear (src : Fin 35) : Cmd 14 35 := .call (clearProgram src 0 1)
def cleared (src : Fin 35) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 35) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

abbrev pushFalse (stack : Fin 35) : Cmd 14 35 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push stack 0))

def pushed (stack : Fin 35) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks stack (false :: d.stacks stack)⟩

theorem pushFalse_eval (stack : Fin 35) (d : Data) :
    Eval (pushFalse stack) 2 d (pushed stack d) := by
  let middle : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  have h₁ : Eval (RecordPrograms.atom (.set 0 false)) 1 d middle := by
    apply Eval.base
    simpa [middle, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 14) (s := 35) 0 false) d
  have h₂ : Eval (RecordPrograms.atom (.push stack 0)) 1 middle (pushed stack d) := by
    apply Eval.base
    simpa [middle, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using
      StructuredProgram.Eval.atom (StructuredProgram.Atom.push (r := 14) (s := 35) stack 0) middle
  exact h₁.seq h₂

def regPort : Fin 3 → Fin 14 := ![11, 12, 13]
def flags (regs : Fin 14 → Bool) : Fin 14 → Bool :=
  Function.update (Function.update (Function.update regs 11 false) 12 true) 13 false

def emitPort (stream : Stream) : Fin 4 → Fin 35 := ![31, 0, stream.port, 34]
def reversePort (stream : Stream) : Fin 4 → Fin 35 := ![stream.port, 0, 25, 34]

theorem regPort_injective : Function.Injective regPort := by decide
theorem emitPort_injective (stream : Stream) : Function.Injective (emitPort stream) := by
  cases stream <;> decide
theorem reversePort_injective (stream : Stream) : Function.Injective (reversePort stream) := by
  cases stream <;> decide

abbrev emit (stream : Stream) : Cmd 14 35 :=
  liftCommand SubexpNormalizeProgram.emitEveryRecord 0 2 regPort (emitPort stream)

def emitted (stream : Stream) (bits : List Bool) (d : Data) : Data :=
  ⟨flags d.regs, Function.update (Function.update d.stacks stream.port
    (true :: (Encoding.frame bits ++ d.stacks stream.port))) 34 []⟩

theorem emit_eval (stream : Stream) (bits : List Bool) (d : Data)
    (hp : d.stacks 34 = bits.reverse) :
    Eval (emit stream) (5 * bits.length + 13) d (emitted stream bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 11) (d.regs 12) (d.regs 13)
    (d.stacks 31) (d.stacks 0) (d.stacks stream.port) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 31) (d.stacks 0)
    (true :: (Encoding.frame bits ++ d.stacks stream.port)) []
  have ha : a = projectState regPort (emitPort stream) d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ emitPort, hp]
  have hb : embedState regPort (emitPort stream) d b = emitted stream bits d := by
    apply embedState_eq_of_ports _ _ _ _ _ regPort_injective (emitPort_injective stream)
    · intro i; fin_cases i <;> simp [b, emitted, regPort, flags,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h11 : i ≠ 11 := fun h => hi ⟨0, h.symm⟩
      have h12 : i ≠ 12 := fun h => hi ⟨1, h.symm⟩
      have h13 : i ≠ 13 := fun h => hi ⟨2, h.symm⟩
      simp [emitted, flags, h11, h12, h13]
    · intro i; cases stream <;> fin_cases i <;>
        simp [b, emitted, emitPort, Stream.port, SubexpNormalizeProgram.filterState]
    · intro i hi
      have ho : i ≠ stream.port := fun h => hi ⟨2, h.symm⟩
      have hp : i ≠ 34 := fun h => hi ⟨3, h.symm⟩
      simp [emitted, ho, hp]
  have he := eval_liftCommand (SubexpNormalizeProgram.emitEveryRecord_eval bits
    (d.stacks 31) (d.stacks 0) (d.stacks stream.port)
    (d.regs 11) (d.regs 12) (d.regs 13)) 0 2 regPort (emitPort stream) d
    regPort_injective (emitPort_injective stream)
  change Eval (emit stream) (5 * bits.length + 12 + 1)
    (embedState regPort (emitPort stream) d a) (embedState regPort (emitPort stream) d b) at he
  rw [ha, embedState_project _ _ _ regPort_injective (emitPort_injective stream), hb] at he
  simpa only [Nat.add_assoc] using he

abbrev reverseCall (stream : Stream) : Cmd 14 35 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    regPort (reversePort stream))

/-- The local framed-record reversal preserves every word outside its two
stream ports and payload; the dummy port is read but unchanged. -/
theorem reverseCall_eval (stream : Stream) (records : List (List Bool)) (d : Data)
    (hs : d.stacks stream.port = Encoding.encodeList id records)
    (ho : d.stacks 25 = [false]) (hp : d.stacks 34 = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e : Data,
      Eval (reverseCall stream) n d e ∧
      e.stacks = Function.update (Function.update d.stacks stream.port []) 25
        (Encoding.encodeList id records.reverse) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 11) (d.regs 12) (d.regs 13)
    (Encoding.encodeList id records) (d.stacks 0) [false] []
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks 0)
    (Encoding.encodeList id records.reverse) []
  have ha : a = projectState regPort (reversePort stream) d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ reversePort, hs, ho, hp]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] []
    (d.stacks 0) (d.regs 11) (d.regs 12) (d.regs 13)
  simp only [List.append_nil, Encoding.encodeList] at ht
  change Trace SubexpNormalizeProgram.reverseRecordsProgram n (a.withPC _) (b.withPC none) at ht
  rw [ha] at ht
  have he := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram
    regPort (reversePort stream) d regPort_injective (reversePort_injective stream) ht
  let e := embedState regPort (reversePort stream) d b
  refine ⟨n, hn, e, he, ?_⟩
  funext i
  by_cases hsrc : i = stream.port
  · subst i
    have h := embedState_stack regPort (reversePort stream) d b
      (reversePort_injective stream) 0
    cases stream <;> simpa [e, b, reversePort, Stream.port,
      SubexpNormalizeProgram.filterState] using h
  by_cases hout : i = 25
  · subst i
    exact embedState_stack regPort (reversePort stream) d b
      (reversePort_injective stream) 2
  by_cases hpay : i = 34
  · subst i
    have h := embedState_stack regPort (reversePort stream) d b
      (reversePort_injective stream) 3
    cases stream <;> simpa [e, b, reversePort, Stream.port,
      SubexpNormalizeProgram.filterState, hp] using h
  by_cases hzero : i = 0
  · subst i
    have h := embedState_stack regPort (reversePort stream) d b
      (reversePort_injective stream) 1
    cases stream <;> simpa [e, b, reversePort, Stream.port,
      SubexpNormalizeProgram.filterState] using h
  have hi : i ∉ Set.range (reversePort stream) := by
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [reversePort] at hj <;> simp_all
  simpa [hsrc, hout] using embedState_stack_frame regPort (reversePort stream) d b i hi

abbrev reverse (stream : Stream) : Cmd 14 35 :=
  .seq (pushFalse 25) (.seq (reverseCall stream)
    (.seq (transfer 25 34) (transfer 34 stream.port)))

/-- A real in-place whole-record reversal. Both bit transfers are counted;
no list reversal or concatenation is a machine instruction. -/
theorem reverse_eval (stream : Stream) (records : List (List Bool)) (d : Data)
    (hs : d.stacks stream.port = Encoding.encodeList id records)
    (h25 : d.stacks 25 = []) (h34 : d.stacks 34 = []) :
    ∃ n ≤ 16 * (Encoding.encodeList id records).length + 8, ∃ e : Data,
      Eval (reverse stream) n d e ∧
      e.stacks = Function.update d.stacks stream.port (Encoding.encodeList id records.reverse) := by
  let a := pushed 25 d
  have ha : a.stacks stream.port = Encoding.encodeList id records := by
    cases stream <;> simpa [a, pushed, Stream.port] using hs
  obtain ⟨n, hn, b, he, hb⟩ := reverseCall_eval stream records a ha
    (by simp [a, pushed, h25]) (by simp [a, pushed, h34])
  let c := transferred 25 34 b
  let e := transferred 34 stream.port c
  have hb25 : b.stacks 25 = Encoding.encodeList id records.reverse := by simp [hb]
  have hc34 : c.stacks 34 = (Encoding.encodeList id records.reverse).reverse := by
    cases stream <;> simp [c, transferred, transferStacks, hb, a, pushed, h34, Stream.port]
  refine ⟨2 + (n + ((3 * (b.stacks 25).length + 3) +
    (3 * (c.stacks 34).length + 3))), ?_, e, ?_, ?_⟩
  · rw [hb25, hc34, List.length_reverse,
      ExecLiteralDedupProgram.encoded_reverse_length]
    omega
  · exact (pushFalse_eval 25 d).seq (he.seq
      ((transfer_eval 25 34 (by decide) b).seq
        (transfer_eval 34 stream.port (by cases stream <;> decide) c)))
  · funext i
    cases stream <;>
      simp [e, c, transferred, transferStacks, hb, a, pushed, Stream.port,
        Function.update_apply, h25, h34] <;>
      split_ifs <;> simp_all

end SubexponentialSAT.SubexpClauseFamilySupport

end OAI.Algorithms
