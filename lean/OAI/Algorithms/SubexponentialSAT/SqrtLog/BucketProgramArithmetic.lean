import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

abbrev AddData := State 8 9

def addWork : Fin 5 ↪ Fin 9 where
  toFun i := ⟨i.val+4, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def choicePorts (bit : Bool) : Ports 9 where
  left := 2
  right := if bit then 1 else 0
  out := 3
  work := addWork
  out_ne_left := by decide
  out_ne_right := by cases bit <;> decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; cases bit <;> fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev choiceAdd : Cmd 8 9 := .ite 0 (addAt (choicePorts true)) (addAt (choicePorts false))

def addReady (d : AddData) : Prop :=
  d.stacks 3 = [] ∧ ∀ i, d.stacks (addWork i) = []

def addInputLength (d : AddData) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length

/-- Port0 is the common offset W, port1 is W+A, port2 is the accumulator,
port3 receives the sum. The selected assignment bit is register0. All input
and scratch stacks are preserved; the returned word is genuine binary data. -/
theorem choiceAdd_eval (d : AddData) (hd : addReady d) :
    ∃ t ≤ 100*(addInputLength d+1)^2+1, ∃ rf word,
      Eval choiceAdd t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      SubexponentialSAT.BinaryArithmetic.toNat word = SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) +
        (if d.regs 0 then SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)
         else SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)) ∧
      word.length ≤ addInputLength d+1 := by
  have hv (b : Bool) : Valid (choicePorts b) d := hd
  cases hb : d.regs 0 with
  | false =>
      obtain ⟨t, rf, word, he, hw, hl, ht⟩ := addAt_eval (choicePorts false) d (hv false)
      refine ⟨t+1, ?_, rf, word, Eval.ite_false hb he, ?_, ?_⟩
      · have hs : (d.stacks (choicePorts false).left).length +
            (d.stacks (choicePorts false).right).length+1 ≤ addInputLength d+1 := by
          simp [choicePorts, addInputLength]; omega
        exact Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _))) 1
      · simpa [choicePorts, hb] using hw
      · exact hl.trans (by simp [choicePorts, addInputLength]; omega)
  | true =>
      obtain ⟨t, rf, word, he, hw, hl, ht⟩ := addAt_eval (choicePorts true) d (hv true)
      refine ⟨t+1, ?_, rf, word, Eval.ite_true hb he, ?_, ?_⟩
      · have hs : (d.stacks (choicePorts true).left).length +
            (d.stacks (choicePorts true).right).length+1 ≤ addInputLength d+1 := by
          simp [choicePorts, addInputLength]; omega
        exact Nat.add_le_add_right (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _))) 1
      · simpa [choicePorts, hb] using hw
      · exact hl.trans (by simp [choicePorts, addInputLength]; omega)

def choiceAddProgram := compiled choiceAdd 0 3

theorem choiceAdd_runsIn (d : AddData) (hd : addReady d) :
    ∃ e : AddData,
      RunsIn choiceAddProgram (100*(addInputLength d+1)^2+2)
        (d.withPC (some choiceAddProgram.entry)) (e.withPC none) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 3) =
        SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) +
        (if d.regs 0 then SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1)
         else SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0)) ∧
      (∀ i : Fin 9, i ≠ 3 → e.stacks i = d.stacks i) := by
  obtain ⟨t, ht, rf, word, he, hv, hl⟩ := choiceAdd_eval d hd
  refine ⟨⟨rf, Function.update d.stacks 3 word⟩,
    ⟨t+1, by omega, compiled_halt_trace he 0 3⟩, ?_, ?_⟩
  · simpa using hv
  · intro i hi; exact Function.update_of_ne hi _ _

/-- Offset summation is exactly the integer signature translated by hW. -/
def offsetSignature {h : ℕ} (W : ℤ) (row : Fin h → ℤ) (x : Fin h → Bool) : ℤ :=
  ∑ i, if x i then W+row i else W

theorem offsetSignature_eq {h : ℕ} (W : ℤ) (row : Fin h → ℤ) (x : Fin h → Bool) :
    offsetSignature W row x = (h : ℤ)*W + ∑ i, row i*(if x i then 1 else 0) := by
  have hs (i : Fin h) : (if x i then W+row i else W) =
      W + row i*(if x i then 1 else 0) := by cases x i <;> simp
  simp only [offsetSignature, hs, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem offsetSignature_eq_iff {h : ℕ} (W : ℤ) (row : Fin h → ℤ)
    (x y : Fin h → Bool) :
    offsetSignature W row x = offsetSignature W row y ↔
      (∑ i, row i*(if x i then 1 else 0)) = ∑ i, row i*(if y i then 1 else 0) := by
  rw [offsetSignature_eq, offsetSignature_eq]
  exact add_left_cancel_iff

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
