import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Embed a prime-field scalar word as the constant coordinate of a quartet. -/

namespace SubexponentialSAT.Subexp.CorrectionScalarEmbedding

open BitProgram StructuredCalls StackRoutines ModularArithmetic ModularPrograms

abbrev Data := State 10 49
abbrev Word := List Bool

def regMap : Fin 8 → Fin 10 := Fin.castAdd 2
def stackMap : Fin 3 → Fin 49 := ![1, 0, 43]
theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 8 2
theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev pad : Cmd 10 49 := .call (ProgramLinking.liftProgram paddingProgram regMap stackMap)

abbrev command : Cmd 10 49 :=
  .seq (.call (copyProgram 47 1 2 (0 : Fin 10) 1)) pad

theorem command_eval (input shape : Word) (a : Data)
    (hi : a.stacks 0 = input) (hs : a.stacks 47 = shape)
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hlen : input.length ≤ shape.length) :
    ∃ b : Data, Eval command (11 * shape.length + 8) a b ∧
      b.stacks = Function.update (Function.update a.stacks 0 []) 43
        ((padTo shape input).reverse ++ a.stacks 43) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 47 1 a.stacks⟩
  have hcopy := TupleProgram.copy_eval 47 1 2 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) a h2
  let inner : State 8 3 := ⟨a1.regs ∘ regMap, operandStacks shape input (a.stacks 43)⟩
  obtain ⟨rf, ht⟩ := SubexpDenseLiteralPadding.padding_trace_any inner.regs shape input (a.stacks 43)
  have hdrop : input.drop shape.length = [] := List.drop_eq_nil_of_le hlen
  rw [hdrop] at ht
  let last : State 8 3 := ⟨rf, operandStacks [] [] ((padTo shape input).reverse ++ a.stacks 43)⟩
  have hin : embedState regMap stackMap a1 inner = a1 := by
    apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
    · intros; rfl
    · intros; rfl
    · intro j
      fin_cases j <;> simp [inner, a1, stackMap, operandStacks, copyStacks, hi, hs, h1]
    · intros; rfl
  let b := embedState regMap stackMap a1 last
  have hpad : Eval pad (4 * shape.length + 3) a1 b := by
    have he := eval_call_lifted paddingProgram regMap stackMap a1 regMap_injective stackMap_injective
      (a := inner) (b := last) ht
    simpa only [pad, b, hin] using he
  refine ⟨b, ?_, ?_⟩
  · have he := hcopy.seq hpad
    convert he using 1
    rw [hs]
    omega
  · funext j
    by_cases hj : ∃ k, stackMap k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [show b.stacks (stackMap k) = last.stacks k from
        embedState_stack _ _ _ _ stackMap_injective k]
      fin_cases k <;> simp [last, stackMap, operandStacks, h1]
    · rw [show b.stacks j = a1.stacks j from embedState_stack_frame _ _ _ _ j hj]
      have hj0 : j ≠ 0 := fun h => hj ⟨1, h.symm⟩
      have hj1 : j ≠ 1 := fun h => hj ⟨0, h.symm⟩
      have hj43 : j ≠ 43 := fun h => hj ⟨2, h.symm⟩
      simp [a1, copyStacks, hj0, hj1, hj43]

theorem padTo_append_zeros (shape input : Word) (hlen : input.length ≤ shape.length) :
    padTo shape input = input ++ List.replicate (shape.length - input.length) false := by
  induction shape generalizing input with
  | nil =>
      have hi : input = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      simp [hi, padTo]
  | cons bit shape ih =>
      cases input with
      | nil =>
          simp [padTo, ih [] (Nat.zero_le _), List.replicate_succ]
      | cons b input =>
          have hh : input.length ≤ shape.length := by simpa using hlen
          simpa [padTo] using congrArg (List.cons b) (ih input hh)

theorem quartet_shape (shape input : Word) (width : ℕ)
    (hs : shape.length = 4 * width) (hi : input.length = width) :
    padTo shape input = input ++ List.replicate (3 * width) false := by
  rw [padTo_append_zeros shape input (by omega), hs, hi]
  congr 2
  omega

end SubexponentialSAT.Subexp.CorrectionScalarEmbedding

end OAI.Algorithms
