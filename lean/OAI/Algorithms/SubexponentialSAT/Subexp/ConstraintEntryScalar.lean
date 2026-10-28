import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixNegationProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarOneProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! The scalar part of a constraint entry: subtract a matrix entry from the
runtime diagonal bit. Both branches execute fixed modular-arithmetic code. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryScalar

open BitProgram StructuredCalls StackRoutines BinaryArithmetic MatrixWordEncoding

abbrev Data := State 8 10

def negPorts : Fin 9 → Fin 10 := Fin.castAdd 1
def addPorts : Fin 8 → Fin 10 := Fin.castAdd 2

theorem negPorts_injective : Function.Injective negPorts := Fin.castAdd_injective _ _
theorem addPorts_injective : Function.Injective addPorts := Fin.castAdd_injective _ _

abbrev negate : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram MatrixNegationProgram.program id negPorts)

abbrev makeOne : Cmd 8 10 := ScalarOneProgram.command 9 1 8 0 1

abbrev add : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram ModularRingPrograms.wordAddProgram id addPorts)

/-- Register 7 is read before any scalar subroutine can overwrite it. -/
abbrev command : Cmd 8 10 := .ite 7 (.seq negate (.seq makeOne add)) negate

def state (p : ℕ) (regs : Fin 8 → Bool) (x : ZMod p) (right : List Bool) : Data :=
  ⟨regs, fun j => if j = 0 then word p x else if j = 1 then right
    else if j = 5 then modulus p else if j = 9 then word p 0 else []⟩

variable (p : ℕ) [Fact p.Prime]

theorem negate_eval (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ n ≤ 6073 * (width p + 1)^2 + 1, ∃ regs',
      Eval negate n (state p regs x []) (state p regs' (-x) []) := by
  obtain ⟨regs', n, hn, ht⟩ := MatrixNegationProgram.program_runsIn p regs x
  have hstart : projectState id negPorts (state p regs x []) =
      MatrixNegationProgram.state p regs x := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [state, negPorts,
          SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
          ModularRingPrograms.extendSeven, ModularDivisionPrograms.resting,
          ModularDivisionPrograms.seven]
  rw [← hstart] at ht
  have he := eval_call_from_state MatrixNegationProgram.program id negPorts
    (state p regs x []) Function.injective_id negPorts_injective ht
  have hfinish : embedState id negPorts (state p regs x [])
      (MatrixNegationProgram.state p regs' (-x)) = state p regs' (-x) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id negPorts_injective
    · intros; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j
      fin_cases j <;>
        simp [state, negPorts, MatrixNegationProgram.state,
          SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
          ModularRingPrograms.extendSeven, ModularDivisionPrograms.resting,
          ModularDivisionPrograms.seven]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      simp [state, h0]
  exact ⟨n, hn, regs', by simpa only [negate, hfinish] using he⟩

theorem makeOne_eval (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ regs', Eval makeOne (7 * width p + 8) (state p regs x [])
      (state p regs' x (word p 1)) := by
  obtain ⟨regs', he⟩ := ScalarOneProgram.canonical_eval p (9 : Fin 10) 1 8
    (0 : Fin 8) 1 (by decide) (by decide) (by decide) (by decide)
    (state p regs x []) (by simp [state]) (by simp [state]) (by simp [state])
  have hf : (⟨regs', Function.update (state p regs x []).stacks 1 (word p 1)⟩ : Data) =
      state p regs' x (word p 1) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    by_cases h1 : j = 1
    · subst j; simp [state]
    · simp [state, h1]
  exact ⟨regs', by simpa only [makeOne, hf] using he⟩

theorem add_eval (regs : Fin 8 → Bool) (x y : ZMod p) :
    ∃ n ≤ 6000 * (width p + 1)^2, ∃ regs',
      Eval add n (state p regs x (word p y)) (state p regs' (x + y) []) := by
  obtain ⟨regs', out, ⟨n, hn, ht⟩, hl, hv⟩ :=
    ModularRingPrograms.wordAdd_value regs (word p x) (word p y) (modulus p)
      (width p) (word_length p x) (word_length p y) (by simp)
      (modulus_positive p) (by simpa only [modulus_value] using modulus_capacity p)
  have hc : BinaryArithmetic.toNat out < p := by
    rw [hv, modulus_value]
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  have hvalue : (BinaryArithmetic.toNat out : ZMod p) = x + y := by
    rw [hv, modulus_value, ZMod.natCast_mod, Nat.cast_add,
      word_field_value, word_field_value]
  have hout := word_unique p (x + y) out hl hc hvalue
  subst out
  have hstart : projectState id addPorts (state p regs x (word p y)) =
      (⟨regs, ModularRingPrograms.extendSeven
        (ModularRingPrograms.scalarInput (word p x) (word p y) (modulus p)) []⟩ :
        State 8 8) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [state, addPorts,
        ModularRingPrograms.extendSeven, ModularRingPrograms.scalarInput,
        ModularDivisionPrograms.seven]
  change Trace ModularRingPrograms.wordAddProgram n
    ((⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput (word p x) (word p y) (modulus p)) []⟩ :
      State 8 8).withPC (some ModularRingPrograms.wordAddProgram.entry))
    ((⟨regs', ModularRingPrograms.extendSeven
      (ModularDivisionPrograms.resting (word p (x + y)) (modulus p) []) []⟩ :
      State 8 8).withPC none) at ht
  rw [← hstart] at ht
  have he := eval_call_from_state ModularRingPrograms.wordAddProgram id addPorts
    (state p regs x (word p y)) Function.injective_id addPorts_injective ht
  have hfinish : embedState id addPorts (state p regs x (word p y))
      (⟨regs', ModularRingPrograms.extendSeven
        (ModularDivisionPrograms.resting (word p (x + y)) (modulus p) []) []⟩ : State 8 8) =
      state p regs' (x + y) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id addPorts_injective
    · intros; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j
      fin_cases j <;> simp [state, addPorts, ModularRingPrograms.extendSeven,
        ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      simp [state, h0, h1]
  exact ⟨n, hn, regs', by simpa only [add, hfinish] using he⟩

def result (flag : Bool) (x : ZMod p) : ZMod p := (if flag then 1 else 0) - x

theorem command_eval (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ n ≤ 13000 * (width p + 1)^2, ∃ regs',
      Eval command n (state p regs x []) (state p regs' (result p (regs 7) x) []) := by
  obtain ⟨nn, hnn, rn, hn⟩ := negate_eval p regs x
  cases hflag : regs 7 with
  | false =>
      refine ⟨nn + 1, by nlinarith only [hnn, Nat.zero_le (width p)], rn, ?_⟩
      have he := Eval.ite_false (yes := .seq negate (.seq makeOne add)) hflag hn
      simpa only [command, result, hflag, Bool.false_eq_true, ite_false, zero_sub] using he
  | true =>
      obtain ⟨ro, ho⟩ := makeOne_eval p rn (-x)
      obtain ⟨na, hna, ra, ha⟩ := add_eval p ro (-x) 1
      refine ⟨nn + (7 * width p + 8 + na) + 1, ?_, ra, ?_⟩
      · nlinarith only [hnn, hna, Nat.zero_le (width p)]
      · have he := Eval.ite_true (no := negate) hflag (hn.seq (ho.seq ha))
        have hx : (-x : ZMod p) + 1 = 1 - x := by ring
        simpa only [command, result, hflag, ite_true, hx] using he

def program := compiled command 0 0

theorem program_runsIn (regs : Fin 8 → Bool) (x : ZMod p) :
    ∃ regs', RunsIn program (13000 * (width p + 1)^2 + 1)
      ((state p regs x []).withPC (some program.entry))
      ((state p regs' (result p (regs 7) x) []).withPC none) := by
  obtain ⟨n, hn, regs', he⟩ := command_eval p regs x
  exact ⟨regs', n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 0 0⟩

end SubexponentialSAT.Subexp.ConstraintEntryScalar

end OAI.Algorithms
