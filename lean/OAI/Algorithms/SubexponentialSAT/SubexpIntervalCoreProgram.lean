import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.CounterPredProgram

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 10 → List Bool
abbrev Data := State 8 32

abbrev port (i : Fin 10) : Fin 32 := ⟨i.val, by omega⟩

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 10 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 10) :
    (state r w).stacks (port i) = w i := by simp [state, port]

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

theorem state_work (r : Regs) (w : Words) (i : Fin 32) (hi : 10 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 10 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 10) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 10
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have := congrArg Fin.val he
      simp only [] at this
      omega
    simp [state, Function.update_apply, hj, hji]

def inputWords (r Q R : List Bool) : Words := ![r, Q, R, [], [], [], [], [], [], []]

def width (r Q R : List Bool) : ℕ := r.length + Q.length + R.length + 1

theorem width_pos (r Q R : List Bool) : 0 < width r Q R := by unfold width; omega

abbrev copyCmd (a b : Fin 10) : Cmd 8 32 :=
  ArithmeticExpressionSupport.copyCmd (port a) (port b) 16

theorem copy_eval (regs : Regs) (w : Words) (a b : Fin 10)
    (hab : a ≠ b) (hb : w b = []) :
    Eval (copyCmd a b) (7 * (w a).length + 5) (state regs w)
      (state (readRegs regs 0 1 none) (Function.update w b (w a))) := by
  have hp (i : Fin 10) : port i ≠ (16 : Fin 32) := by
    intro he
    have := congrArg Fin.val he
    simp only [] at this
    omega
  have h := ArithmeticExpressionSupport.copy_eval (port a) (port b) 16 (state regs w)
    (by intro he; exact hab (Fin.ext (congrArg (fun j : Fin 32 => j.val) he)))
    (hp a) (hp b).symm
    (by simpa only [state_port] using hb) (state_work _ _ _ (by decide))
  simpa only [copyCmd, state_port, state_update, state_regs] using h

def predPorts (i : Fin 10) : CounterForPrograms.Ports 8 32 where
  register := ⟨fun j => ⟨j.val, by omega⟩, by
    intro a b h
    exact Fin.ext (congrArg (fun j : Fin 8 => j.val) h)⟩
  counter := port i
  scratch := 15
  counter_ne_scratch := by
    intro h
    have := congrArg Fin.val h
    simp only [] at this
    omega

abbrev predCmd (i : Fin 10) : Cmd 8 32 := CounterPredProgram.predCmd (predPorts i)

theorem pred_eval (regs : Regs) (w : Words) (i : Fin 10) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (predCmd i) t (state regs w) (state rf (Function.update w i word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w i) - 1 ∧ word.length ≤ (w i).length ∧
      t ≤ 20 * ((w i).length + 1) := by
  obtain ⟨t, rf, word, ht, he, hv, hl⟩ :=
    CounterPredProgram.pred_correct (predPorts i) (state regs w)
      (state_work _ _ 15 (by decide))
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [predCmd, predPorts, state_update] using he
  · simpa only [predPorts, state_port] using hv
  · simpa only [predPorts, state_port] using hl
  · simpa only [predPorts, state_port] using ht

def arithmeticPorts (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 32 where
  left := port a
  right := port b
  out := port o
  work := ⟨fun j => ⟨10 + j.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩
  out_ne_left := by intro h; exact hoa (Fin.ext (congrArg (fun j : Fin 32 => j.val) h))
  out_ne_right := by intro h; exact hob (Fin.ext (congrArg (fun j : Fin 32 => j.val) h))
  work_ne_left := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = a.val at hv
    omega
  work_ne_right := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = b.val at hv
    omega
  work_ne_out := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = o.val at hv
    omega

abbrev multiplyCmd (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev addCmd (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

theorem arithmetic_valid (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state regs w) := by
  constructor
  · simpa only [arithmeticPorts, state_port] using ho
  · intro i
    apply state_work
    change 10 ≤ 10 + i.val
    omega

theorem multiply_eval (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (multiplyCmd a b o hoa hob) t (state regs w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1)^2 := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state regs w)
      (arithmetic_valid regs w a b o hoa hob ho)
  exact ⟨t, rf, word,
    by simpa only [multiplyCmd, arithmeticPorts, state_update] using he,
    by simpa only [arithmeticPorts, state_port] using hv,
    by simpa only [arithmeticPorts, state_port] using hl,
    by simpa only [arithmeticPorts, state_port] using ht⟩

theorem add_eval (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (addCmd a b o hoa hob) t (state regs w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1)^2 := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state regs w)
      (arithmetic_valid regs w a b o hoa hob ho)
  exact ⟨t, rf, word,
    by simpa only [addCmd, arithmeticPorts, state_update] using he,
    by simpa only [arithmeticPorts, state_port] using hv,
    by simpa only [arithmeticPorts, state_port] using hl,
    by simpa only [arithmeticPorts, state_port] using ht⟩

abbrev command : Cmd 8 32 :=
  .seq (copyCmd 0 4) (.seq (predCmd 4)
    (.seq (copyCmd 1 5) (.seq (predCmd 5)
      (.seq (multiplyCmd 5 4 6 (by decide) (by decide))
        (.seq (multiplyCmd 2 0 7 (by decide) (by decide))
          (addCmd 0 0 8 (by decide) (by decide)))))))

theorem command_eval (regs : Regs) (r Q R : List Bool) :
    ∃ (t : ℕ) (rf : Regs) (w : Words),
      Eval command t (state regs (inputWords r Q R)) (state rf w) ∧
      w 0 = r ∧ w 1 = Q ∧ w 2 = R ∧ w 3 = [] ∧ w 9 = [] ∧
      BinaryArithmetic.toNat (w 6) = (BinaryArithmetic.toNat Q - 1) * (BinaryArithmetic.toNat r - 1) ∧
      BinaryArithmetic.toNat (w 7) = BinaryArithmetic.toNat R * BinaryArithmetic.toNat r ∧ BinaryArithmetic.toNat (w 8) = 2 * BinaryArithmetic.toNat r ∧
      (∀ j, (w j).length ≤ 2 * width r Q R) ∧ t ≤ 1000 * (width r Q R)^2 := by
  let w0 := inputWords r Q R
  let w1 := Function.update w0 4 r
  let r1 := readRegs regs 0 1 none
  have hc1 := copy_eval regs w0 0 4 (by decide) (by rfl)
  obtain ⟨t1, r2, rp, hp1, hv1, hl1, ht1⟩ := pred_eval r1 w1 4
  let w2 := Function.update w1 4 rp
  let w3 := Function.update w2 5 Q
  let r3 := readRegs r2 0 1 none
  have hc2 := copy_eval r2 w2 1 5 (by decide) (by simp [w2, w1, w0, inputWords])
  obtain ⟨t2, r4, qp, hp2, hv2, hl2, ht2⟩ := pred_eval r3 w3 5
  let w4 := Function.update w3 5 qp
  obtain ⟨t3, r5, prod, hm1, hv3, hl3, ht3⟩ :=
    multiply_eval r4 w4 5 4 6 (by decide) (by decide) (by
      simp [w4, w3, w2, w1, w0, inputWords])
  let w5 := Function.update w4 6 prod
  obtain ⟨t4, r6, radius, hm2, hv4, hl4, ht4⟩ :=
    multiply_eval r5 w5 2 0 7 (by decide) (by decide) (by
      simp [w5, w4, w3, w2, w1, w0, inputWords])
  let w6 := Function.update w5 7 radius
  obtain ⟨t5, r7, den, ha, hv5, hl5, ht5⟩ :=
    add_eval r6 w6 0 0 8 (by decide) (by decide) (by
      simp [w6, w5, w4, w3, w2, w1, w0, inputWords])
  let w7 := Function.update w6 8 den
  simp only [w1, Function.update_self] at hv1 hl1 ht1
  simp only [w3, Function.update_self] at hv2 hl2 ht2
  simp [w6, w5, w4, w3, w2, w1, w0, inputWords] at hv3 hl3 ht3 hv4 hl4 ht4 hv5 hl5 ht5
  have he : Eval command ((7 * r.length + 5) + (t1 +
      ((7 * Q.length + 5) + (t2 + (t3 + (t4 + t5))))))
      (state regs w0) (state r7 w7) :=
    hc1.seq (hp1.seq (hc2.seq (hp2.seq (hm1.seq (hm2.seq ha)))))
  refine ⟨_, r7, w7, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simpa [w7, w6, w5, hv1, hv2] using hv3
  · simpa [w7, w6] using hv4
  · simpa [w7, two_mul] using hv5
  · intro j
    fin_cases j <;> simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
    all_goals dsimp [width] at *; omega
  · let W := width r Q R
    have hW : 1 ≤ W := width_pos r Q R
    have hWsq : W ≤ W^2 := by nlinarith
    have h3w : qp.length + rp.length + 1 ≤ W := by dsimp [W, width]; omega
    have h4w : R.length + r.length + 1 ≤ W := by dsimp [W, width]; omega
    have h5w : r.length + r.length + 1 ≤ 2 * W := by dsimp [W, width]; omega
    have hb3 := ht3.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h3w 2))
    have hb4 := ht4.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h4w 2))
    have hb5 := ht5.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h5w 2))
    have hlr : r.length ≤ W := by dsimp [W, width]; omega
    have hlq : Q.length ≤ W := by dsimp [W, width]; omega
    change _ ≤ 1000 * W^2
    nlinarith only [hb3, hb4, hb5, ht1, ht2, hlr, hlq, hW, hWsq]

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
