import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-!
# Actual binary-to-unary conversion

The finite controller consumes a little-endian binary counter on stack 0.
Each positive iteration pushes one true bit onto stack 1. Stack 2 is counter
scratch. The cleanup empties the counter and resets every Boolean register.
The numeric value controls execution through stack instructions only.
-/

namespace SubexponentialSAT.CounterConversions

open BitProgram StructuredProgram StructuredCalls CounterPrograms CounterForPrograms

abbrev Data := StructuredProgram.State 3 3

def ports : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 2
  counter_ne_scratch := by decide

def zeroRegs : Fin 3 → Bool := fun _ => false

def state (regs : Fin 3 → Bool) (counter output : List Bool) : Data :=
  ⟨regs, ![counter, output, []]⟩

abbrev push (bit : Bool) : StructuredCalls.Cmd 3 3 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push 1 0)))

def pushed (bit : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks 1 (bit :: d.stacks 1)⟩

theorem push_eval (bit : Bool) (d : Data) :
    StructuredCalls.Eval (push bit) 2 d (pushed bit d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) bit) d).seq
    (StructuredProgram.Eval.atom (.push (1 : Fin 3) 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

abbrev clear : StructuredCalls.Cmd 3 3 := .call (StackRoutines.clearProgram 0 0 1)

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 []⟩

theorem clear_eval (d : Data) :
    StructuredCalls.Eval clear (2 * (d.stacks 0).length + 3) d (cleared d) :=
  .call _ (ListRegisterProgram.clear_run 0 0 1 d.regs d.stacks)

abbrev reset : StructuredCalls.Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def resetState (d : Data) : Data := ⟨zeroRegs, d.stacks⟩

theorem reset_eval (d : Data) : StructuredCalls.Eval reset 3 d (resetState d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) d).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply StructuredCalls.Eval.base
  convert h using 1
  apply CounterForPrograms.data_ext
  · funext i
    fin_cases i <;>
      simp [resetState, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

def outputInvariant (tail : List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 1 = List.replicate i true ++ tail

theorem outputInvariant_stable (tail : List Bool) :
    FrameStable ports (outputInvariant tail) := by
  intro i a b hab hi
  exact (hab 1 (by decide) (by decide)).symm.trans hi

theorem push_spec (tail : List Bool) :
    BodySpec ports (push true) (outputInvariant tail) (fun _ => 2) := by
  intro i d hi hs _
  refine ⟨2, pushed true d, le_rfl, push_eval true d, ?_, ?_, ?_⟩
  · simp [pushed, ports]
  · simpa [pushed, ports] using hs
  · change d.stacks 1 = List.replicate i true ++ tail at hi
    simp [outputInvariant, pushed, List.replicate_succ, hi]

abbrev unaryCmd : StructuredCalls.Cmd 3 3 :=
  .seq (CounterForPrograms.forCmd ports (push true)) (.seq clear reset)

def coreBound (bits : List Bool) : ℕ :=
  2 * value bits + (value bits + 1) * (16 * bits.length + 16) + 2 * bits.length + 6

/-- The suffix is arbitrary, which permits both unary strings and terminated
natural-number fields to use the same fixed conversion loop. -/
theorem unary_correct (d : Data) (hs : d.stacks 2 = []) :
    ∃ n, StructuredCalls.Eval unaryCmd n d
      (state zeroRegs [] (List.replicate (value (d.stacks 0)) true ++ d.stacks 1)) ∧
      n ≤ coreBound (d.stacks 0) := by
  obtain ⟨n, e, he, hi, hz, hw, hes, hn⟩ := CounterForPrograms.for_correct
    ports (push true) (outputInvariant (d.stacks 1)) (fun _ => 2)
    (outputInvariant_stable _) (push_spec _) d hs (by simp [outputInvariant])
  have ho : e.stacks 1 = List.replicate (value (d.stacks 0)) true ++ d.stacks 1 := hi
  have hw' : (e.stacks 0).length = (d.stacks 0).length := hw
  have hs' : e.stacks 2 = [] := hes
  have heq : resetState (cleared e) =
      state zeroRegs [] (List.replicate (value (d.stacks 0)) true ++ d.stacks 1) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext j
      fin_cases j <;> simp [resetState, cleared, state, ho, hs']
  refine ⟨n + ((2 * (e.stacks 0).length + 3) + 3), ?_, ?_⟩
  · rw [← heq]
    exact he.seq ((clear_eval e).seq (reset_eval (cleared e)))
  · have hn' : n ≤ value (d.stacks 0) * 2 +
        (value (d.stacks 0) + 1) * (16 * (d.stacks 0).length + 16) := by
      simpa [ports, budgetSum_const] using hn
    rw [hw']
    dsimp [coreBound]
    omega

theorem unary_eval (regs : Fin 3 → Bool) (bits tail : List Bool) :
    ∃ n, StructuredCalls.Eval unaryCmd n (state regs bits tail)
      (state zeroRegs [] (List.replicate (value bits) true ++ tail)) ∧ n ≤ coreBound bits := by
  simpa [state] using unary_correct (state regs bits tail) rfl

abbrev encodeNatCmd : StructuredCalls.Cmd 3 3 := .seq (push false) unaryCmd

theorem encodeNat_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval encodeNatCmd n (state regs bits [])
      (state zeroRegs [] (Encoding.encodeNat (value bits))) ∧ n ≤ coreBound bits + 2 := by
  let d := state regs bits []
  obtain ⟨n, he, hn⟩ := unary_correct (pushed false d) (by simp [pushed, d, state])
  refine ⟨2 + n, ?_, ?_⟩
  · have h := (push_eval false d).seq he
    simpa [encodeNatCmd, pushed, d, state, Encoding.encodeNat] using h
  · have hn' : n ≤ coreBound bits := by simpa [pushed, d, state] using hn
    omega

def runtimeBound (bits : List Bool) : ℕ := 32 * (value bits + 1) * (bits.length + 1)

theorem coreBound_le (bits : List Bool) : coreBound bits + 3 ≤ runtimeBound bits := by
  dsimp [coreBound, runtimeBound]
  nlinarith [Nat.zero_le (value bits * bits.length)]

def unaryProgram := StructuredCalls.compiled unaryCmd (0 : Fin 3) 1
def encodeNatProgram := StructuredCalls.compiled encodeNatCmd (0 : Fin 3) 1

theorem unary_runs (regs : Fin 3 → Bool) (bits tail : List Bool) :
    BitProgram.RunsIn unaryProgram (runtimeBound bits)
      ((state regs bits tail).withPC (some unaryProgram.entry))
      ((state zeroRegs [] (List.replicate (value bits) true ++ tail)).withPC none) := by
  obtain ⟨n, he, hn⟩ := unary_eval regs bits tail
  exact ⟨n + 1, by have := coreBound_le bits; omega,
    StructuredCalls.compiled_halt_trace he 0 1⟩

theorem encodeNat_runs (regs : Fin 3 → Bool) (bits : List Bool) :
    BitProgram.RunsIn encodeNatProgram (runtimeBound bits)
      ((state regs bits []).withPC (some encodeNatProgram.entry))
      ((state zeroRegs [] (Encoding.encodeNat (value bits))).withPC none) := by
  obtain ⟨n, he, hn⟩ := encodeNat_eval regs bits
  exact ⟨n + 1, by have := coreBound_le bits; omega,
    StructuredCalls.compiled_halt_trace he 0 1⟩

theorem unary_primitive (regs : Fin 3 → Bool) (bits tail : List Bool) :
    Computation.RunsIn (BitProgram.primitive unaryProgram).step
      (BitProgram.primitiveOverhead unaryProgram * runtimeBound bits)
      (BitProgram.primitiveCfg unaryProgram
        ((state regs bits tail).withPC (some unaryProgram.entry)))
      (BitProgram.primitiveCfg unaryProgram
        ((state zeroRegs [] (List.replicate (value bits) true ++ tail)).withPC none)) :=
  BitProgram.primitive_execution unaryProgram (unary_runs regs bits tail)

theorem encodeNat_primitive (regs : Fin 3 → Bool) (bits : List Bool) :
    Computation.RunsIn (BitProgram.primitive encodeNatProgram).step
      (BitProgram.primitiveOverhead encodeNatProgram * runtimeBound bits)
      (BitProgram.primitiveCfg encodeNatProgram
        ((state regs bits []).withPC (some encodeNatProgram.entry)))
      (BitProgram.primitiveCfg encodeNatProgram
        ((state zeroRegs [] (Encoding.encodeNat (value bits))).withPC none)) :=
  BitProgram.primitive_execution encodeNatProgram (encodeNat_runs regs bits)

end SubexponentialSAT.CounterConversions

end OAI.Algorithms
