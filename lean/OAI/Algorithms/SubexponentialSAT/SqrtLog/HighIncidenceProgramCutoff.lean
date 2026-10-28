import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence
import OAI.Algorithms.SubexponentialSAT.SubexpCeilingProgram
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual runtime multiplication and ceiling division for the high-incidence
integer threshold. Inputs are binary S,t,n; the output is binary ceil(S*t/n).
Counting S from scope records and converting the result to unary are separate
physical frontend obligations, not operations hidden in this specification. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 12
abbrev Code := Cmd 8 12

def state (regs : Fin 8 → Bool) (mass scale dimension : List Bool) : Data :=
  ⟨regs, ![mass, scale, dimension, [], [], [], [], [], [], [], [], []]⟩

def work : Fin 5 ↪ Fin 12 where
  toFun i := ⟨7 + i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def ports : ArithmeticCalls.Ports 12 where
  left := 0
  right := 1
  out := 3
  work := work
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def ceilingPorts : Fin 8 → Fin 12 := ![4, 7, 8, 9, 10, 2, 3, 5]
theorem ceilingPorts_injective : Function.Injective ceilingPorts := by decide

def command : Code := .seq (ArithmeticCalls.multiplyAt ports)
  (.call (ProgramLinking.liftProgram SubexpCeilingProgram.program id ceilingPorts))
def program := compiled command 0 5

def bound (mass scale dimension : List Bool) :=
  100 * (mass.length + scale.length + 1)^2 +
    500 * (mass.length + scale.length + dimension.length + 2)^2 + 1

theorem command_eval (regs : Fin 8 → Bool) (mass scale dimension : List Bool)
    (hn : 0 < BinaryArithmetic.toNat dimension) :
    ∃ time b, Eval command time (state regs mass scale dimension) b ∧
      time + 1 ≤ bound mass scale dimension ∧
      BinaryArithmetic.toNat (b.stacks 5) = (BinaryArithmetic.toNat mass * BinaryArithmetic.toNat scale) ⌈/⌉ BinaryArithmetic.toNat dimension ∧
      (b.stacks 5).length ≤ mass.length + scale.length + 2 ∧
      b.stacks 0 = mass ∧ b.stacks 1 = scale ∧ b.stacks 2 = dimension := by
  let a := state regs mass scale dimension
  have ha : ArithmeticCalls.Valid ports a := by
    constructor
    · rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨tm, rm, product, hm, hp, hl, ht⟩ := ArithmeticCalls.multiplyAt_eval ports a ha
  let mid : Data := ⟨rm, Function.update a.stacks 3 product⟩
  have hp' : BinaryArithmetic.toNat product = BinaryArithmetic.toNat mass * BinaryArithmetic.toNat scale := hp
  have hl' : product.length ≤ mass.length + scale.length + 1 := hl
  have ht' : tm ≤ 100 * (mass.length + scale.length + 1)^2 := ht
  have hproject : projectState id ceilingPorts mid =
      SubexpCeilingProgram.inputState rm dimension product := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨localResult, hout, tc, htc, hc⟩ := SubexpCeilingProgram.run_output rm dimension product hn
  rw [← hproject] at hc
  let b := embedState id ceilingPorts mid localResult
  have he := eval_call_from_state SubexpCeilingProgram.program id ceilingPorts mid
    Function.injective_id ceilingPorts_injective hc
  have hs (i : Fin 8) : b.stacks (ceilingPorts i) = localResult.stacks i :=
    embedState_stack _ _ _ _ ceilingPorts_injective i
  refine ⟨tm + tc, b, hm.seq he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcBound := SubexpCeilingProgram.runtimeBound_le dimension product
      (L := mass.length + scale.length + dimension.length + 1) (by omega) (by omega)
    have hcBound' : SubexpCeilingProgram.runtimeBound dimension product ≤
        500 * (mass.length + scale.length + dimension.length + 2)^2 := by
      simpa [Nat.add_assoc] using hcBound
    dsimp [bound]
    omega
  · rw [show b.stacks 5 = localResult.stacks 7 from hs 7, hout.1, hp']
    rfl
  · rw [show b.stacks 5 = localResult.stacks 7 from hs 7]
    exact hout.2.1.trans (by omega)
  · change (embedState id ceilingPorts mid localResult).stacks 0 = mass
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    rfl
  · change (embedState id ceilingPorts mid localResult).stacks 1 = scale
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    rfl
  · exact (hs 5).trans (SubexpCeilingProgram.output_modulus dimension product localResult hout)

theorem program_runsIn (regs : Fin 8 → Bool) (mass scale dimension : List Bool)
    (hn : 0 < BinaryArithmetic.toNat dimension) :
    ∃ b : Data, RunsIn program (bound mass scale dimension)
      ((state regs mass scale dimension).withPC (some program.entry)) (b.withPC none) ∧
      BinaryArithmetic.toNat (b.stacks 5) = (BinaryArithmetic.toNat mass * BinaryArithmetic.toNat scale) ⌈/⌉ BinaryArithmetic.toNat dimension := by
  obtain ⟨time, b, he, ht, hv, _⟩ := command_eval regs mass scale dimension hn
  exact ⟨b, ⟨time+1, ht, compiled_halt_trace he 0 5⟩, hv⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

end OAI.Algorithms
