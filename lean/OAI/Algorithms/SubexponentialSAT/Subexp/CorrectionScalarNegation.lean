import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNegationProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! A framed prime-field negation call for the increasing-coordinate row loop. -/

namespace SubexponentialSAT.Subexp.CorrectionScalarNegation

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic
open ModularRingPrograms ModularDivisionPrograms

abbrev Data := State 10 49
abbrev Word := List Bool

def regMap : Fin 8 → Fin 10 := Fin.castAdd 2
def stackMap : Fin 9 → Fin 49 := ![0, 1, 2, 3, 4, 29, 6, 7, 46]
theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 8 2
theorem stackMap_injective : Function.Injective stackMap := by decide

abbrev command : Cmd 10 49 :=
  .call (ProgramLinking.liftProgram SubexpNegationProgram.negationProgram regMap stackMap)

theorem command_eval (input modulus constant : Word) (width : ℕ) (a : Data)
    (hi : a.stacks 0 = input) (hm : a.stacks 29 = modulus) (hc : a.stacks 46 = constant)
    (hwork : ∀ j : Fin 49, j ∈ [1, 2, 3, 4, 6, 7] → a.stacks j = [])
    (hiw : input.length = width) (hcw : constant.length = width)
    (hmw : modulus.length ≤ width + 1)
    (hmpos : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ width)
    (hconstant : BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1) :
    ∃ n ≤ 6010 * (width + 1) ^ 2, ∃ output : Word, ∃ b : Data,
      Eval command n a b ∧ output.length = width ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) = -(BinaryArithmetic.toNat input : ZMod (BinaryArithmetic.toNat modulus)) ∧
      b.stacks = Function.update a.stacks 0 output := by
  let inner : State 8 9 := ⟨a.regs ∘ regMap, SubexpNegationProgram.state input modulus constant⟩
  obtain ⟨rf, output, ⟨n, hn, ht⟩, hw, hv⟩ := SubexpNegationProgram.negation_cast inner.regs
    input modulus constant width hiw hcw hmw hmpos hcapacity hconstant
  let last : State 8 9 := ⟨rf, SubexpNegationProgram.state output modulus constant⟩
  have hin : embedState regMap stackMap a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
    · intros; rfl
    · intros; rfl
    · intro j
      fin_cases j <;>
        simp [inner, stackMap, SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
          extendSeven, resting, seven, hi, hm, hc,
          hwork 1 (by simp), hwork 2 (by simp), hwork 3 (by simp),
          hwork 4 (by simp), hwork 6 (by simp), hwork 7 (by simp)]
    · intros; rfl
  let b := embedState regMap stackMap a last
  have he : Eval command n a b := by
    have h := eval_call_lifted SubexpNegationProgram.negationProgram regMap stackMap a
      regMap_injective stackMap_injective (a := inner) (b := last) ht
    simpa only [command, b, hin] using h
  refine ⟨n, hn, output, b, he, hw, hv, ?_⟩
  funext j
  by_cases hj : ∃ k, stackMap k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (stackMap k) = last.stacks k from
      embedState_stack _ _ _ _ stackMap_injective k]
    fin_cases k <;>
      simp [last, stackMap, SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
        extendSeven, resting, seven, hm, hc,
        hwork 1 (by simp), hwork 2 (by simp), hwork 3 (by simp),
        hwork 4 (by simp), hwork 6 (by simp), hwork 7 (by simp)]
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    simp [h0]

end SubexponentialSAT.Subexp.CorrectionScalarNegation

end OAI.Algorithms
