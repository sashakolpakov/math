import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramAdd

namespace OAI.Algorithms

/-! A fixed cleanup adapter makes signed arithmetic reusable inside loops. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def pairState (regs : Fin 8 → Bool) (positive negative : List Bool) : Data :=
  ⟨regs, fun j => if j = 0 then positive else if j = 1 then negative else []⟩

abbrev finishCommand : Cmd 8 15 :=
  .seq (clearList [0,1,2,3,4,5,7,8])
    (.seq (ArithmeticCalls.copyAt 6 0 10)
      (.seq (ArithmeticCalls.copyAt 9 1 10) (clearList [6,9])))

theorem finishCommand_eval (d : Data) (B : ℕ)
    (hb : ∀ j : Fin 15, (d.stacks j).length ≤ B)
    (hf : ∀ j : Fin 15, 10 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 34*B+40, ∃ regs,
      Eval finishCommand t d (pairState regs (d.stacks 6) (d.stacks 9)) := by
  let a := clearedList [0,1,2,3,4,5,7,8] d
  obtain ⟨tc, htc, hec⟩ := clearList_eval_bounded [0,1,2,3,4,5,7,8] d B
    (fun j _ => hb j)
  have ha0 : a.stacks 0 = [] := by simp [a]
  have ha1 : a.stacks 1 = [] := by simp [a]
  have ha6 : a.stacks 6 = d.stacks 6 := by simp [a]
  have ha9 : a.stacks 9 = d.stacks 9 := by simp [a]
  have ha10 : a.stacks 10 = [] := by simpa [a] using hf 10 (by decide)
  let b := ArithmeticCalls.afterCopy 6 0 a
  have he0 := ArithmeticCalls.copyAt_eval 6 0 10 a (by decide) (by decide)
    (by decide) ha0 ha10
  have hb1 : b.stacks 1 = [] := by simpa [b, ArithmeticCalls.afterCopy] using ha1
  have hb10 : b.stacks 10 = [] := by simpa [b, ArithmeticCalls.afterCopy] using ha10
  let c := ArithmeticCalls.afterCopy 9 1 b
  have he1 := ArithmeticCalls.copyAt_eval 9 1 10 b (by decide) (by decide)
    (by decide) hb1 hb10
  have hc6 : c.stacks 6 = d.stacks 6 := by simpa [c, b, ArithmeticCalls.afterCopy] using ha6
  have hc9 : c.stacks 9 = d.stacks 9 := by simpa [c, b, ArithmeticCalls.afterCopy] using ha9
  obtain ⟨td, htd, hed⟩ := clearList_eval_bounded [6,9] c B (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · simpa only [hc6] using hb 6
    · simpa only [hc9] using hb 9)
  let out := clearedList [6,9] c
  have hout : out = pairState out.regs (d.stacks 6) (d.stacks 9) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      have hf10 := hf 10 (by decide)
      have hf11 := hf 11 (by decide)
      have hf12 := hf 12 (by decide)
      have hf13 := hf 13 (by decide)
      have hf14 := hf 14 (by decide)
      fin_cases j <;>
        simp [ c, b, a, clearedList, clearedAt, ArithmeticCalls.afterCopy,
          hf10, hf11, hf12, hf13, hf14]
  refine ⟨tc + ((7*(a.stacks 6).length+5) + ((7*(b.stacks 9).length+5)+td)),
    ?_, out.regs, ?_⟩
  · have hb6 := hb 6
    have hb9 := hb 9
    simp only [List.length_cons, List.length_nil] at htc htd
    have hb9' : b.stacks 9 = d.stacks 9 := by
      simpa [b, ArithmeticCalls.afterCopy] using ha9
    rw [ha6, hb9']
    omega
  · rw [← hout]
    exact hec.seq (he0.seq (he1.seq hed))

private theorem initial_stack_bound (d : Data) (hd : Ready d) (j : Fin 15) :
    (d.stacks j).length ≤ inputLength d := by
  by_cases hj : j.val < 4
  · fin_cases j <;> simp_all [inputLength] <;> omega
  · rw [hd j (by omega)]
    simp

/-- Reusable signed multiplication: result returns on 0/1 and all other
stacks are empty. The source operands on 0/1 and 2/3 are consumed. -/
abbrev multiplyReuseCommand : Cmd 8 15 := .seq multiplyCommand finishCommand

theorem multiplyReuseCommand_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval multiplyReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ 2*inputLength d+6 := by
  obtain ⟨tm, htm, m, hem, hv, hp, hn, hf⟩ := multiplyCommand_eval d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    rw [hf j (Or.inr hj), hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, by omega⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]

/-- Reusable signed addition with a linear bound on the total result-word size. -/
abbrev addReuseCommand : Cmd 8 15 := .seq addCommand finishCommand

theorem addReuseCommand_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval addReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ inputLength d+2 := by
  obtain ⟨tm, htm, m, hem, hv, hl, hf⟩ := addCommand_eval d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    have hj6 : j ≠ 6 := by intro h; have : j.val = 6 := congrArg Fin.val h; omega
    have hj9 : j ≠ 9 := by intro h; have : j.val = 9 := congrArg Fin.val h; omega
    rw [hf j hj6 hj9, hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, hl⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
