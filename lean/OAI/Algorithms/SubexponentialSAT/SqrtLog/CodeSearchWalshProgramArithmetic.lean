import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgramCount
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def work : Fin 5 ↪ Fin 14 where
  toFun i := ⟨i.val + 8, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega
def ports (i : Fin 4) : Ports 14 where
  left := ![0,0,1,4] i
  right := ![1,3,5,1] i
  out := ![4,5,6,7] i
  work := work
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

abbrev arithmetic : Cmd 8 14 := .seq count (.seq (multiplyAt (ports 0))
  (.seq (multiplyAt (ports 1)) (.seq (Subexp.TupleProgram.pushConst 5 0 false)
    (.seq (addAt (ports 2)) (addAt (ports 3))))))
def inputLength (d : ArithData) : ℕ := (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length
def ready (d : ArithData) : Prop := ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []

theorem arithmetic_eval (d : ArithData) (hd : ready d) :
    ∃ t ≤ 600 * (2 * inputLength d + 4)^2, ∃ e : ArithData,
      Eval arithmetic t d e ∧
      BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
      (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * inputLength d + 4) ∧
      (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j) := by
  have hwork (i : Fin 5) : 3 ≤ (work i).val := by
    change 3 ≤ i.val + 8
    omega
  obtain ⟨tc, htc, rc, wc, hec, hvc, hlc⟩ := count_eval d
    (hd 3 (by decide)) (hd 12 (by decide)) (hd 13 (by decide))
  let a : ArithData := ⟨rc, Function.update d.stacks 3 wc⟩
  have hv0 : Valid (ports 0) a := by
    constructor
    · simpa [a, ports] using hd 4 (by decide)
    · intro i
      have hi : work i ≠ 3 := by
        intro h
        have hval : i.val + 8 = 3 := congrArg Fin.val h
        omega
      simpa [a, ports, hi] using hd (work i) (hwork i)
  obtain ⟨t0, r0, w0, he0, hv0', hl0, ht0⟩ := multiplyAt_eval (ports 0) a hv0
  let b : ArithData := ⟨r0, Function.update a.stacks 4 w0⟩
  have hv1 : Valid (ports 1) b := by
    constructor
    · simpa [b, a, ports] using hd 5 (by decide)
    · intro i
      have hi : work i ≠ 4 := (ports 0).work_ne_out i
      simpa [b, ports, hi] using hv0.2 i
  obtain ⟨t1, r1, w1, he1, hv1', hl1, ht1⟩ := multiplyAt_eval (ports 1) b hv1
  let c : ArithData := ⟨r1, Function.update b.stacks 5 w1⟩
  let c' := Subexp.TupleProgram.pushedState 5 0 false c
  have heS := Subexp.TupleProgram.pushConst_eval 5 0 false c
  have hv2 : Valid (ports 2) c' := by
    constructor
    · simpa [c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hd 6 (by decide)
    · intro i
      have hi : work i ≠ 5 := (ports 1).work_ne_out i
      simpa [c', Subexp.TupleProgram.pushedState, c, ports, hi] using hv1.2 i
  obtain ⟨t2, r2, w2, he2, hv2', hl2, ht2⟩ := addAt_eval (ports 2) c' hv2
  let f : ArithData := ⟨r2, Function.update c'.stacks 6 w2⟩
  have hv3 : Valid (ports 3) f := by
    constructor
    · simpa [f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hd 7 (by decide)
    · intro i
      have hi : work i ≠ 6 := (ports 2).work_ne_out i
      simpa [f, ports, hi] using hv2.2 i
  obtain ⟨t3, r3, w3, he3, hv3', hl3, ht3⟩ := addAt_eval (ports 3) f hv3
  let e : ArithData := ⟨r3, Function.update f.stacks 7 w3⟩
  have hl0' : w0.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := by
    simpa [a, ports] using hl0
  have hl1' : w1.length ≤ (d.stacks 0).length + wc.length + 1 := by
    simpa [b, a, ports] using hl1
  have hl2' : w2.length ≤ (d.stacks 1).length + w1.length + 2 := by
    simpa [c', Subexp.TupleProgram.pushedState, c, b, a, ports, Nat.add_assoc] using hl2
  have hl3' : w3.length ≤ w0.length + (d.stacks 1).length + 1 := by
    simpa [f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hl3
  have hlen : (d.stacks 2).length ≤ inputLength d := by unfold inputLength; omega
  have htc' : tc ≤ 100 * (2 * inputLength d + 4)^2 := by
    have hm := Nat.mul_le_mul hlen
      (show 8 * (d.stacks 2).length + 10 ≤ 8 * inputLength d + 10 by omega)
    have hs := Nat.mul_le_mul_left 7 hlen
    nlinarith only [htc, hm, hs]
  have ht0' : t0 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht0.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [a, ports, inputLength]; omega
  have ht1' : t1 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht1.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [b, a, ports, inputLength]; omega
  have ht2' : t2 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht2.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [c', c, b, a, ports, inputLength]; omega
  have ht3' : t3 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht3.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [f, c', c, b, a, ports, inputLength]; omega
  refine ⟨tc + (t0 + (t1 + (2 + (t2+t3)))), ?_, e,
    hec.seq (he0.seq (he1.seq (heS.seq (he2.seq he3)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 16 ≤ (2 * inputLength d + 4)^2 :=
      Nat.pow_le_pow_left (show 4 ≤ 2 * inputLength d + 4 by omega) 2
    omega
  · simpa [e, f, c', Subexp.TupleProgram.pushedState, c, b, a] using hvc
  · simpa [e, f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hv0'
  · simp [e, f, c', c]
    simp [b, a, ports, hvc] at hv1'
    rw [hv1']; ring
  · simp [e, f]
    simp [c', c, b, a, ports] at hv2'
    simp [b, a, ports, hvc] at hv1'
    rw [hv2', hv1']; ring
  · simp [e]
    simp [f, c', c, b, a, ports] at hv3'
    simp [a, ports] at hv0'
    rw [hv3', hv0']
  · intro j hjlo hjhi
    have hj : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      simp [e, f, c', c, b, a, inputLength] <;> omega
  · intro j hj
    have h3 : j ≠ 3 := by intro h; have hv : j.val = 3 := congrArg Fin.val h; omega
    have h4 : j ≠ 4 := by intro h; have hv : j.val = 4 := congrArg Fin.val h; omega
    have h5 : j ≠ 5 := by intro h; have hv : j.val = 5 := congrArg Fin.val h; omega
    have h6 : j ≠ 6 := by intro h; have hv : j.val = 6 := congrArg Fin.val h; omega
    have h7 : j ≠ 7 := by intro h; have hv : j.val = 7 := congrArg Fin.val h; omega
    simp [e, f, c', c, b, a, h3, h4, h5, h6, h7]

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
