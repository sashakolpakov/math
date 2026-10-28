import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Actual normalization of a positive binary counter word

The logarithm preparer reverses its input and removes high zeroes together
with the leading one. This wrapper physically restores that one and reverses
the remaining word. Positive inputs therefore retain their exact value and
have width log2(value)+1. All three registers and both work stacks are clean
at return, even when the incoming registers are arbitrary.
-/

namespace SubexponentialSAT.CounterNormalizeProgram

open BitProgram StructuredProgram StructuredCalls CounterPrograms

abbrev Data := StructuredProgram.State 3 3

def normalized (bits : List Bool) : List Bool :=
  (true :: SubexpParameterProgram.trimTail bits.reverse).reverse

theorem normalized_value (bits : List Bool) (hp : 0 < value bits) :
    value (normalized bits) = value bits := by
  induction bits using List.reverseRecOn with
  | nil => simp [value] at hp
  | append_singleton bits bit ih =>
    cases bit with
    | false =>
      have hp' : 0 < value bits := by
        simpa [SubexpParameterProgram.value_append, value] using hp
      simpa [normalized, List.reverse_append, SubexpParameterProgram.trimTail,
        SubexpParameterProgram.value_append, value] using ih hp'
    | true =>
      simp [normalized, List.reverse_append, SubexpParameterProgram.trimTail]

theorem normalized_length (bits : List Bool) :
    (normalized bits).length = Nat.log2 (value bits) + 1 := by
  simp [normalized, SubexpParameterProgram.trimTail_reverse_length]

theorem normalized_eq_fixedBits (bits : List Bool) (hp : 0 < value bits) :
    normalized bits = SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits) := by
  have hcap : value bits < 2 ^ (Nat.log2 (value bits) + 1) := by
    simpa only [normalized_value bits hp, normalized_length] using
      SubexpParameterProgram.value_lt_two_pow_length (normalized bits)
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [normalized_length, SubexpLiftRing.fixedBits_length]
  · rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hcap,
      ← CounterPrograms.value_eq_toNat]
    exact normalized_value bits hp

def zeroRegs : Fin 3 → Bool := fun _ => false

def state (regs : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨regs, ![input, output, []]⟩

private theorem data_ext {a b : Data} (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) :
    a = b := by cases a; cases b; cases hr; cases hs; rfl

abbrev reset : StructuredCalls.Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

theorem reset_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    StructuredCalls.Eval reset 3 (state regs bits []) (state zeroRegs bits []) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) false) (state regs bits [])).seq
    ((StructuredProgram.Eval.atom (.set (1 : Fin 3) false) _).seq
      (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) _))
  apply StructuredCalls.Eval.base
  convert h using 1
  apply data_ext
  · funext i
    fin_cases i <;>
      simp [state, zeroRegs, Atom.eval, Atom.instr, State.ofCfg, execInstr]
  · rfl

theorem prepare_eval (bits : List Bool) :
    ∃ n, n ≤ 6 * bits.length + 9 ∧
      StructuredCalls.Eval (.call SubexpParameterProgram.prepareLogProgram) n
        (state zeroRegs bits [])
        (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpParameterProgram.prepareLog_runs bits
  have ha : initial SubexpParameterProgram.prepareLogProgram bits =
      (state zeroRegs bits []).withPC (some SubexpParameterProgram.prepareLogProgram.entry) := by
    simp only [initial, state, State.withPC ]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hb : terminal SubexpParameterProgram.prepareLogProgram
        (SubexpParameterProgram.trimTail bits.reverse) =
      (state zeroRegs [] (SubexpParameterProgram.trimTail bits.reverse)).withPC none := by
    simp only [terminal, state, State.withPC ]
    congr 1
    funext i
    fin_cases i <;> rfl
  exact ⟨n, hn, .call _ (by simpa only [ha, hb] using ht)⟩

abbrev pushTop : StructuredCalls.Cmd 3 3 :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push 1 0)))

def pushed (d : Data) : Data :=
  ⟨Function.update d.regs 0 true, Function.update d.stacks 1 (true :: d.stacks 1)⟩

theorem pushTop_eval (d : Data) : StructuredCalls.Eval pushTop 2 d (pushed d) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 3) true) d).seq
    (StructuredProgram.Eval.atom (.push (1 : Fin 3) 0) _)
  exact .base (by simpa [pushed, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr] using h)

abbrev reverseProgram : Program 3 3 4 := StackRoutines.transferProgram 1 0 0 1

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 1 0 d.stacks⟩

theorem reverse_eval (d : Data) :
    StructuredCalls.Eval (.call reverseProgram) (3 * (d.stacks 1).length + 3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 1 0 0 1 (by decide) (by decide) d.regs d.stacks)

abbrev restore : StructuredCalls.Cmd 3 3 := .seq pushTop (.call reverseProgram)

theorem restore_eval (tail : List Bool) :
    StructuredCalls.Eval restore (3 * tail.length + 8) (state zeroRegs [] tail)
      (state zeroRegs (true :: tail).reverse []) := by
  have h := (pushTop_eval (state zeroRegs [] tail)).seq
    (reverse_eval (pushed (state zeroRegs [] tail)))
  have heq : transferred (pushed (state zeroRegs [] tail)) =
      state zeroRegs (true :: tail).reverse [] := by
    apply data_ext
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, zeroRegs, readRegs]
    · funext i
      fin_cases i <;> simp [transferred, pushed, state, StackRoutines.transferStacks]
  convert h using 1
  · simp [pushed, state]
    omega
  · exact heq.symm

abbrev command : StructuredCalls.Cmd 3 3 :=
  .seq reset (.seq (.call SubexpParameterProgram.prepareLogProgram) restore)

theorem command_eval (regs : Fin 3 → Bool) (bits : List Bool) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (normalized bits) []) ∧ n ≤ 9 * bits.length + 20 := by
  obtain ⟨n, hn, he⟩ := prepare_eval bits
  refine ⟨3 + (n + (3 * (SubexpParameterProgram.trimTail bits.reverse).length + 8)),
    (reset_eval regs bits).seq (he.seq (restore_eval _)), ?_⟩
  have hlen : (SubexpParameterProgram.trimTail bits.reverse).length ≤ bits.length := by
    simpa using SubexpParameterProgram.trimTail_length_le bits.reverse
  omega

theorem normalize_eval (regs : Fin 3 → Bool) (bits : List Bool) (hp : 0 < value bits) :
    ∃ n, StructuredCalls.Eval command n (state regs bits [])
      (state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []) ∧
      n ≤ 9 * bits.length + 20 := by
  simpa only [normalized_eq_fixedBits bits hp] using command_eval regs bits

abbrev program : Program 3 3 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 0

@[simp] theorem command_size : StructuredCalls.size command = 19 := by
  simp [ StructuredCalls.size, StructuredProgram.size]

theorem normalize_runs (regs : Fin 3 → Bool) (bits : List Bool) (hp : 0 < value bits) :
    BitProgram.RunsIn program (9 * bits.length + 21)
      ((state regs bits []).withPC (some program.entry))
      ((state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []).withPC none) := by
  obtain ⟨n, he, hn⟩ := normalize_eval regs bits hp
  exact ⟨n + 1, by omega, StructuredCalls.compiled_halt_trace he 0 0⟩

theorem program_runs (bits : List Bool) (hp : 0 < value bits) :
    BitProgram.RunsIn program (9 * bits.length + 21) (initial program bits)
      (terminal program (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits))) := by
  have ha : initial program bits = (state zeroRegs bits []).withPC (some program.entry) := by
    simp only [initial, state, State.withPC ]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hb : terminal program
        (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) =
      (state zeroRegs (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)) []).withPC none := by
    simp only [terminal, state, State.withPC ]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [ha, hb] using normalize_runs zeroRegs bits hp

theorem program_primitive (bits : List Bool) (hp : 0 < value bits) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (9 * bits.length + 21))
      (BitProgram.primitiveCfg program (initial program bits))
      (BitProgram.primitiveCfg program
        (terminal program (SubexpLiftRing.fixedBits (Nat.log2 (value bits) + 1) (value bits)))) :=
  BitProgram.primitive_execution program (program_runs bits hp)

end SubexponentialSAT.CounterNormalizeProgram

end OAI.Algorithms
