import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramResources

namespace OAI.Algorithms

/-! Fixed-control addition for integer difference-pair words. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open SubexponentialSAT.BinaryArithmetic

def addWork : Fin 5 ↪ Fin 15 where
  toFun i := ⟨i.val+10, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def addPositivePorts : Ports 15 where
  left := 0
  right := 2
  out := 6
  work := addWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def addNegativePorts : Ports 15 where
  left := 1
  right := 3
  out := 9
  work := addWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev addCommand : Cmd 8 15 := .seq (addAt addPositivePorts) (addAt addNegativePorts)
def addProgram := compiled addCommand 0 6

theorem addCommand_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ 200 * (inputLength d + 1)^2, ∃ e : Data,
      Eval addCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length + (e.stacks 9).length ≤ inputLength d + 2 ∧
      (∀ j : Fin 15, j ≠ 6 → j ≠ 9 → e.stacks j = d.stacks j) := by
  have hp : Valid addPositivePorts d := by
    constructor
    · exact hd 6 (by decide)
    · intro i; exact hd (addWork i) (by change 4 ≤ i.val + 10; omega)
  obtain ⟨tp, rp, wp, hep, hvp, hlp, htp⟩ := addAt_eval addPositivePorts d hp
  let middle : Data := ⟨rp, Function.update d.stacks 6 wp⟩
  have hn : Valid addNegativePorts middle := by
    constructor
    · simpa [middle, addNegativePorts] using hd 9 (by decide)
    · intro i
      have hi : addWork i ≠ 6 := by fin_cases i <;> decide
      simpa [middle, addNegativePorts, hi] using
        hd (addWork i) (by change 4 ≤ i.val + 10; omega)
  obtain ⟨tn, rn, wn, hen, hvn, hln, htn⟩ := addAt_eval addNegativePorts middle hn
  let out : Data := ⟨rn, Function.update middle.stacks 9 wn⟩
  have hpbound : (d.stacks addPositivePorts.left).length +
      (d.stacks addPositivePorts.right).length + 1 ≤ inputLength d + 1 := by
    dsimp [addPositivePorts, inputLength]; omega
  have hnbound : (middle.stacks addNegativePorts.left).length +
      (middle.stacks addNegativePorts.right).length + 1 ≤ inputLength d + 1 := by
    simp [middle, addNegativePorts, inputLength]; omega
  have htp' := htp.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hpbound 2))
  have htn' := htn.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hnbound 2))
  refine ⟨tp+tn, by omega, out, hep.seq hen, ?_, ?_, ?_⟩
  · simp [addPositivePorts] at hvp
    simp [middle, addNegativePorts] at hvn
    simp [out, middle, signedValue, hvp, hvn]
    ring
  · simp [addPositivePorts] at hlp
    simp [middle, addNegativePorts] at hln
    simp [out, middle, inputLength]
    omega
  · intro j h6 h9
    simp [out, middle, h6, h9]

theorem addProgram_runsIn (d : Data) (hd : Ready d) :
    ∃ e : Data,
      RunsIn addProgram (200 * (inputLength d + 1)^2 + 1)
        (d.withPC (some addProgram.entry)) (e.withPC none) ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) := by
  obtain ⟨t, ht, e, he, hv, _⟩ := addCommand_eval d hd
  exact ⟨e, ⟨t+1, by omega, compiled_halt_trace he 0 6⟩, hv⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
