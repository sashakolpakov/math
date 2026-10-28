import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.PowerCalls

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 15 → List Bool
abbrev Data := State 8 22

def port (i : Fin 15) : Fin 22 := i.castAdd 7

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 15 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 15) :
    (state r w).stacks (port i) = w i := by simp [state, port]

theorem state_work (r : Regs) (w : Words) (i : Fin 22) (hi : 15 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 15 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 15) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 15
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 22 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]

def inputWords (s delta Q : List Bool) : Words :=
  ![s, delta, Q, [], [], [], [], [], [], [], [], [], [], [], []]

def work (m : ℕ) (hm : m ≤ 7) : Fin m ↪ Fin 22 where
  toFun i := ⟨15 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem work_ne_port (m : ℕ) (hm : m ≤ 7) (i : Fin m) (j : Fin 15) :
    work m hm i ≠ port j := by
  intro h
  have he : 15 + i.val = j.val := congrArg (fun x : Fin 22 => x.val) h
  have := j.isLt
  omega

def arithmeticPorts (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 22 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 15 7) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 15 7) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

def powerPorts (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) :
    PowerCalls.Ports 22 where
  base := port a
  exponent := port b
  out := port o
  work := work 7 (by decide)
  out_ne_base := by intro h; exact hoa ((Fin.castAdd_injective 15 7) h)
  out_ne_exponent := by intro h; exact hob ((Fin.castAdd_injective 15 7) h)
  work_ne_base := fun i => work_ne_port 7 (by decide) i a
  work_ne_exponent := fun i => work_ne_port 7 (by decide) i b
  work_ne_out := fun i => work_ne_port 7 (by decide) i o

abbrev addCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

abbrev multiplyCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev powerCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  PowerCalls.powerAt (powerPorts a b o hoa hob)

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        (state_work r w (work 5 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        (state_work r w (work 5 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem power_eval (r : Regs) (w : Words) (a b o : Fin 15)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) ^ BinaryArithmetic.toNat (w b) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (w b) * (w a).length ∧
      t ≤ PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 := by
  have hv : PowerCalls.Valid (powerPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [powerPorts, state_port] using ho
    · intro i
      simpa only [powerPorts] using
        (state_work r w (work 7 (by decide) i) (by change 15 ≤ 15 + i.val; omega))
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    PowerCalls.powerAt_spec (powerPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [powerCmd, powerPorts, state_update] using he
  · simpa only [powerPorts, state_port] using hval
  · simpa only [powerPorts, state_port] using hlen
  · simpa only [powerPorts, state_port] using htime

abbrev loadCmd (o : Fin 15) (word : List Bool) : Cmd 8 22 :=
  ArithmeticExpressionSupport.pushWord (port o) word

theorem load_eval (r : Regs) (w : Words) (o : Fin 15)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he

/-- The code depends on the fixed clause width, and not on any input number. -/
abbrev command (k : ℕ) : Cmd 8 22 :=
  .seq (loadCmd 3 [true])
    (.seq (loadCmd 4 k.bits)
      (.seq (addCmd 1 3 5 (by decide) (by decide))
        (.seq (multiplyCmd 2 5 6 (by decide) (by decide))
          (.seq (powerCmd 0 6 7 (by decide) (by decide))
            (.seq (multiplyCmd 0 0 8 (by decide) (by decide))
              (.seq (multiplyCmd 7 7 9 (by decide) (by decide))
                (.seq (multiplyCmd 9 7 10 (by decide) (by decide))
                  (.seq (multiplyCmd 1 4 11 (by decide) (by decide))
                    (.seq (addCmd 3 11 12 (by decide) (by decide))
                      (.seq (multiplyCmd 8 10 13 (by decide) (by decide))
                        (multiplyCmd 13 12 14 (by decide) (by decide))))))))))))

def program (k : ℕ) := compiled (command k) (0 : Fin 22) 14

def inputWidth (k : ℕ) (s delta Q : List Bool) : ℕ :=
  s.length + delta.length + Q.length + k.bits.length + 1

def exponentValue (delta Q : List Bool) : ℕ := BinaryArithmetic.toNat Q * (BinaryArithmetic.toNat delta + 1)

def commonWidth (W E : ℕ) : ℕ := (E + 1) * (W + 1)

/-- A polynomial bound in the numerical exponent and the actual input widths. -/
def powerBound (W E : ℕ) : ℕ :=
  E * (50 * (W + 1) * (2 + (E + 1) * W)) +
    (E + 1) * (16 * (5 * commonWidth W E) + 16) + 3 +
    9 * (5 * commonWidth W E) + 8

def stepBound (W E : ℕ) : ℕ :=
  2 * W + 9 * (100 * (2 * (16 * commonWidth W E) + 1) ^ 2) + powerBound W E

def runtimeBound (k : ℕ) (s delta Q : List Bool) : ℕ :=
  stepBound (inputWidth k s delta Q) (exponentValue delta Q)

theorem stepBound_polynomial (W E : ℕ) :
    stepBound W E ≤ 1000000 * (E + 1) ^ 2 * (W + 1) ^ 2 := by
  let H := commonWidth W E
  have hW : W + 1 ≤ H := by
    exact Nat.le_mul_of_pos_left (W + 1) (Nat.succ_pos E)
  have hH : 1 ≤ H := by omega
  have hE : E + 1 ≤ H := by
    exact Nat.le_mul_of_pos_right (E + 1) (Nat.succ_pos W)
  have hEW : E * (W + 1) ≤ H := by
    exact Nat.mul_le_mul_right (W + 1) (Nat.le_succ E)
  have hWE : (E + 1) * W ≤ H := by
    exact Nat.mul_le_mul_left (E + 1) (Nat.le_succ W)
  have hsq : H ≤ H ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right H hH
  have harith : 100 * (2 * (16 * H) + 1) ^ 2 ≤ 108900 * H ^ 2 := by
    calc
      _ ≤ 100 * (33 * H) ^ 2 := by gcongr; omega
      _ = _ := by ring
  have hfirst : E * (50 * (W + 1) * (2 + (E + 1) * W)) ≤ 150 * H ^ 2 := by
    calc
      _ = 50 * (E * (W + 1)) * (2 + (E + 1) * W) := by ring
      _ ≤ 50 * H * (2 + H) := by gcongr
      _ ≤ 150 * H ^ 2 := by nlinarith only [hsq]
  have hsecond : (E + 1) * (16 * (5 * H) + 16) ≤ 96 * H ^ 2 := by
    calc
      _ ≤ H * (16 * (5 * H) + 16) := Nat.mul_le_mul_right _ hE
      _ ≤ 96 * H ^ 2 := by nlinarith only [hsq]
  have hpower : powerBound W E ≤ 302 * H ^ 2 := by
    change E * (50 * (W + 1) * (2 + (E + 1) * W)) +
      (E + 1) * (16 * (5 * H) + 16) + 3 + 9 * (5 * H) + 8 ≤ _
    nlinarith only [hH, hsq, hfirst, hsecond]
  calc
    stepBound W E ≤ 1000000 * H ^ 2 := by
      change 2 * W + 9 * (100 * (2 * (16 * H) + 1) ^ 2) + powerBound W E ≤ _
      nlinarith only [hW, hsq, harith, hpower]
    _ = 1000000 * (E + 1) ^ 2 * (W + 1) ^ 2 := by
      dsimp [H, commonWidth]
      ring

theorem runtimeBound_polynomial (k : ℕ) (s delta Q : List Bool) :
    runtimeBound k s delta Q ≤
      1000000 * (exponentValue delta Q + 1) ^ 2 * (inputWidth k s delta Q + 1) ^ 2 :=
  stepBound_polynomial _ _

private theorem arithmetic_time_le {a t H : ℕ}
    (ha : a ≤ 2 * (16 * H) + 1)
    (ht : t ≤ 100 * a ^ 2) :
    t ≤ 100 * (2 * (16 * H) + 1) ^ 2 := by
  apply ht.trans
  exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left ha 2)

/-- The returned low-word file records the actual words produced by the code.
No canonical-padding convention is required. -/
structure Output (k : ℕ) (s delta Q : List Bool) (w : Words) : Prop where
  s_preserved : w 0 = s
  delta_preserved : w 1 = delta
  Q_preserved : w 2 = Q
  exponent : BinaryArithmetic.toNat (w 6) = exponentValue delta Q
  blockSize : BinaryArithmetic.toNat (w 7) = BinaryArithmetic.toNat s ^ exponentValue delta Q
  blockThreshold : BinaryArithmetic.toNat (w 14) =
    BinaryArithmetic.toNat s ^ 2 * (BinaryArithmetic.toNat s ^ exponentValue delta Q) ^ 3 * (1 + BinaryArithmetic.toNat delta * k)
  word_length : ∀ i, (w i).length ≤
    16 * commonWidth (inputWidth k s delta Q) (exponentValue delta Q)

private def lengthFile (S D Q K L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 : ℕ) :
    Fin 15 → ℕ := ![S, D, Q, 1, K, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14]

/-- Pure length arithmetic is checked independently of the execution witnesses. -/
private theorem length_estimates (S D Q K W E L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 : ℕ)
    (hW : S + D + Q + K + 1 ≤ W)
    (hl5 : L5 ≤ D + 1 + 1) (hl6 : L6 ≤ Q + L5 + 1)
    (hl7 : L7 ≤ 1 + E * S) (hl8 : L8 ≤ S + S + 1)
    (hl9 : L9 ≤ L7 + L7 + 1) (hl10 : L10 ≤ L9 + L7 + 1)
    (hl11 : L11 ≤ D + K + 1) (hl12 : L12 ≤ 1 + L11 + 1)
    (hl13 : L13 ≤ L8 + L10 + 1) (hl14 : L14 ≤ L13 + L12 + 1) :
    (∀ i, lengthFile S D Q K L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 i ≤
      16 * commonWidth W E) ∧ L6 ≤ 5 * commonWidth W E := by
  let H := commonWidth W E
  have hWH : W + 1 ≤ H := Nat.le_mul_of_pos_left (W + 1) (Nat.succ_pos E)
  have hH : 1 ≤ H := (Nat.succ_le_succ (Nat.zero_le W)).trans hWH
  have hsW : S ≤ W := by omega
  have hsH : S ≤ H := hsW.trans ((Nat.le_succ W).trans hWH)
  have hdH : D ≤ H := (show D ≤ W by omega).trans ((Nat.le_succ W).trans hWH)
  have hqH : Q ≤ H := (show Q ≤ W by omega).trans ((Nat.le_succ W).trans hWH)
  have hkH : K ≤ H := (show K ≤ W by omega).trans ((Nat.le_succ W).trans hWH)
  have hw5 : L5 ≤ 3 * H := by omega
  have hw6 : L6 ≤ 5 * H := by omega
  have hw7 : L7 ≤ H := by
    have hm := Nat.mul_le_mul_left E hsW
    dsimp [H, commonWidth]
    nlinarith only [hl7, hm]
  have hw8 : L8 ≤ 3 * H := by omega
  have hw9 : L9 ≤ 3 * H := by omega
  have hw10 : L10 ≤ 5 * H := by omega
  have hw11 : L11 ≤ H := (hl11.trans (by omega)).trans ((Nat.le_succ W).trans hWH)
  have hw12 : L12 ≤ 3 * H := by omega
  have hw13 : L13 ≤ 9 * H := by omega
  have hw14 : L14 ≤ 13 * H := by omega
  refine ⟨?_, hw6⟩
  intro i
  change lengthFile S D Q K L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 i ≤ 16 * H
  fin_cases i <;> simp [lengthFile] <;> omega

private theorem bounded_update {w : Words} {B : ℕ}
    (h : ∀ i, (w i).length ≤ B) (i : Fin 15) (word : List Bool) (hw : word.length ≤ B) :
    ∀ j, (Function.update w i word j).length ≤ B :=
  (Function.forall_update_iff w (fun _ word => word.length ≤ B)).2
    ⟨hw, fun j _ => h j⟩

private theorem input_bounded (s delta Q : List Bool) (B : ℕ)
    (hs : s.length ≤ B) (hd : delta.length ≤ B) (hq : Q.length ≤ B) :
    ∀ i, (inputWords s delta Q i).length ≤ B := by
  intro i
  fin_cases i <;> simp [inputWords] <;> assumption

private theorem arithmetic_time_bounded {left right t H : ℕ}
    (hl : left ≤ 16 * H) (hr : right ≤ 16 * H)
    (ht : t ≤ 100 * (left + right + 1)^2) :
    t ≤ 100 * (2 * (16 * H) + 1)^2 :=
  arithmetic_time_le (by omega) ht

private theorem power_time_bounded (s exponent : List Bool) (W E t : ℕ)
    (hs : s.length ≤ W) (he : BinaryArithmetic.toNat exponent = E)
    (hw : exponent.length ≤ 5 * commonWidth W E)
    (ht : t ≤ PowerPrograms.runtimeBound s exponent + 9 * exponent.length + 8) :
    t ≤ powerBound W E := by
  apply ht.trans
  simp only [PowerPrograms.runtimeBound, PowerPrograms.workBound,
    PowerPrograms.callbackBound, he, powerBound]
  gcongr

private theorem total_time_bounded (W E K t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 : ℕ)
    (hload : 2 + 2 * K ≤ 2 * W)
    (h5 : t5 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h6 : t6 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h7 : t7 ≤ powerBound W E)
    (h8 : t8 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h9 : t9 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h10 : t10 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h11 : t11 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h12 : t12 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h13 : t13 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2)
    (h14 : t14 ≤ 100 * (2 * (16 * commonWidth W E) + 1)^2) :
    2 + (2 * K + (t5 + (t6 + (t7 + (t8 + (t9 +
      (t10 + (t11 + (t12 + (t13 + t14)))))))))) ≤ stepBound W E := by
  unfold stepBound
  omega

/-- Closed execution of the block-parameter stage, including constant loading,
exponentiation, and all threshold products. -/
theorem command_eval (k : ℕ) (r : Regs) (s delta Q : List Bool) :
    ∃ t rf w, Eval (command k) t (state r (inputWords s delta Q)) (state rf w) ∧
      Output k s delta Q w ∧ t ≤ runtimeBound k s delta Q := by
  let v0 := inputWords s delta Q
  obtain ⟨r1, he1⟩ := load_eval r v0 3 [true] (by simp [v0, inputWords])
  let v1 := Function.update v0 3 [true]
  obtain ⟨r2, he2⟩ := load_eval r1 v1 4 k.bits (by simp [v1, v0, inputWords])
  let v2 := Function.update v1 4 k.bits
  obtain ⟨t5, r5, word5, he5, hv5, hl5, ht5⟩ :=
    add_eval r2 v2 1 3 5 (by decide) (by decide) (by simp [v2, v1, v0, inputWords])
  simp [v2, v1, v0, inputWords, BinaryArithmetic.toNat] at hv5 hl5 ht5
  let v3 := Function.update v2 5 word5
  obtain ⟨t6, r6, word6, he6, hv6, hl6, ht6⟩ :=
    multiply_eval r5 v3 2 5 6 (by decide) (by decide)
      (by simp [v3, v2, v1, v0, inputWords])
  simp [v3, v2, v1, v0, inputWords] at hv6 hl6 ht6
  let v4 := Function.update v3 6 word6
  obtain ⟨t7, r7, word7, he7, hv7, hl7, ht7⟩ :=
    power_eval r6 v4 0 6 7 (by decide) (by decide)
      (by simp [v4, v3, v2, v1, v0, inputWords])
  simp [v4, v3, v2, v1, v0, inputWords] at hv7 hl7 ht7
  let v5 := Function.update v4 7 word7
  obtain ⟨t8, r8, word8, he8, hv8, hl8, ht8⟩ :=
    multiply_eval r7 v5 0 0 8 (by decide) (by decide)
      (by simp [v5, v4, v3, v2, v1, v0, inputWords])
  simp [v5, v4, v3, v2, v1, v0, inputWords] at hv8 hl8 ht8
  let v6 := Function.update v5 8 word8
  obtain ⟨t9, r9, word9, he9, hv9, hl9, ht9⟩ :=
    multiply_eval r8 v6 7 7 9 (by decide) (by decide)
      (by simp [v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v6, v5, v4, v3, v2, v1, v0, inputWords] at hv9 hl9 ht9
  let v7 := Function.update v6 9 word9
  obtain ⟨t10, r10, word10, he10, hv10, hl10, ht10⟩ :=
    multiply_eval r9 v7 9 7 10 (by decide) (by decide)
      (by simp [v7, v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v7, v6, v5, v4, v3, v2, v1, v0, inputWords] at hv10 hl10 ht10
  let v8 := Function.update v7 10 word10
  obtain ⟨t11, r11, word11, he11, hv11, hl11, ht11⟩ :=
    multiply_eval r10 v8 1 4 11 (by decide) (by decide)
      (by simp [v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords,
    ArithmeticExpressionSupport.bits_value] at hv11 hl11 ht11
  let v9 := Function.update v8 11 word11
  obtain ⟨t12, r12, word12, he12, hv12, hl12, ht12⟩ :=
    add_eval r11 v9 3 11 12 (by decide) (by decide)
      (by simp [v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords, BinaryArithmetic.toNat] at hv12 hl12 ht12
  let v10 := Function.update v9 12 word12
  obtain ⟨t13, r13, word13, he13, hv13, hl13, ht13⟩ :=
    multiply_eval r12 v10 8 10 13 (by decide) (by decide)
      (by simp [v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords] at hv13 hl13 ht13
  let v11 := Function.update v10 13 word13
  obtain ⟨t14, r14, word14, he14, hv14, hl14, ht14⟩ :=
    multiply_eval r13 v11 13 12 14 (by decide) (by decide)
      (by simp [v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords])
  simp [v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords] at hv14 hl14 ht14
  let v12 := Function.update v11 14 word14
  have hexec := he1.seq (he2.seq (he5.seq (he6.seq (he7.seq (he8.seq (he9.seq
    (he10.seq (he11.seq (he12.seq (he13.seq he14))))))))))
  clear he1 he2 he5 he6 he7 he8 he9 he10 he11 he12 he13 he14
  let W := inputWidth k s delta Q
  let E := exponentValue delta Q
  let H := commonWidth W E
  have hE : BinaryArithmetic.toNat word6 = E := by simpa [E, exponentValue, hv5] using hv6
  have hN : BinaryArithmetic.toNat word7 = BinaryArithmetic.toNat s ^ E := by simpa [hE] using hv7
  have hD : BinaryArithmetic.toNat word14 = BinaryArithmetic.toNat s ^ 2 * (BinaryArithmetic.toNat s ^ E) ^ 3 * (1 + BinaryArithmetic.toNat delta * k) := by
    rw [hv14, hv13, hv12, hv11, hv10, hv9, hv8, hN]
    ring
  have hsum : s.length + delta.length + Q.length + k.bits.length + 1 ≤ W := Nat.le_refl _
  rw [hE] at hl7
  obtain ⟨hmax, hw6⟩ := length_estimates s.length delta.length Q.length k.bits.length W E
    word5.length word6.length word7.length word8.length word9.length word10.length
    word11.length word12.length word13.length word14.length hsum
    hl5 hl6 hl7 hl8 hl9 hl10 hl11 hl12 hl13 hl14
  have hb0 : ∀ i, (v0 i).length ≤ 16 * H :=
    input_bounded s delta Q (16 * H) (hmax 0) (hmax 1) (hmax 2)
  have hb1 := bounded_update hb0 3 [true] (hmax 3)
  have hb2 := bounded_update hb1 4 k.bits (hmax 4)
  have hb3 := bounded_update hb2 5 word5 (hmax 5)
  have hb4 := bounded_update hb3 6 word6 (hmax 6)
  have hb5 := bounded_update hb4 7 word7 (hmax 7)
  have hb6 := bounded_update hb5 8 word8 (hmax 8)
  have hb7 := bounded_update hb6 9 word9 (hmax 9)
  have hb8 := bounded_update hb7 10 word10 (hmax 10)
  have hb9 := bounded_update hb8 11 word11 (hmax 11)
  have hb10 := bounded_update hb9 12 word12 (hmax 12)
  have hb11 := bounded_update hb10 13 word13 (hmax 13)
  have hb12 := bounded_update hb11 14 word14 (hmax 14)
  let A := 100 * (2 * (16 * H) + 1) ^ 2
  have ha5 : t5 ≤ A := arithmetic_time_bounded (hmax 1) (hmax 3) ht5
  have ha6 : t6 ≤ A := arithmetic_time_bounded (hmax 2) (hmax 5) ht6
  have ha8 : t8 ≤ A := arithmetic_time_bounded (hmax 0) (hmax 0) ht8
  have ha9 : t9 ≤ A := arithmetic_time_bounded (hmax 7) (hmax 7) ht9
  have ha10 : t10 ≤ A := arithmetic_time_bounded (hmax 9) (hmax 7) ht10
  have ha11 : t11 ≤ A := arithmetic_time_bounded (hmax 1) (hmax 4) ht11
  have ha12 : t12 ≤ A := arithmetic_time_bounded (hmax 3) (hmax 11) ht12
  have ha13 : t13 ≤ A := arithmetic_time_bounded (hmax 8) (hmax 10) ht13
  have ha14 : t14 ≤ A := arithmetic_time_bounded (hmax 13) (hmax 12) ht14
  have hsW : s.length ≤ W := by dsimp [W, inputWidth]; omega
  have hp7 : t7 ≤ powerBound W E := power_time_bounded s word6 W E t7 hsW hE hw6 ht7
  have hload : 2 + 2 * k.bits.length ≤ 2 * W := by dsimp [W, inputWidth]; omega
  let total := 2 + (2 * k.bits.length + (t5 + (t6 + (t7 + (t8 + (t9 +
    (t10 + (t11 + (t12 + (t13 + t14))))))))))
  refine ⟨total, r14, v12, ?_, ?_, ?_⟩
  · exact hexec
  · constructor
    · simp [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords]
    · simp [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords]
    · simp [v12, v11, v10, v9, v8, v7, v6, v5, v4, v3, v2, v1, v0, inputWords]
    · simpa [v12, v11, v10, v9, v8, v7, v6, v5, v4, E] using hE
    · simpa [v12, v11, v10, v9, v8, v7, v6, v5, E] using hN
    · simpa [v12, E] using hD
    · exact hb12
  · exact total_time_bounded W E k.bits.length t5 t6 t7 t8 t9 t10 t11 t12 t13 t14
      hload ha5 ha6 hp7 ha8 ha9 ha10 ha11 ha12 ha13 ha14

/-- The same stage as a concrete finite instruction trace. -/
theorem run_value (k : ℕ) (r : Regs) (s delta Q : List Bool) :
    ∃ rf w, Output k s delta Q w ∧
      RunsIn (program k) (runtimeBound k s delta Q + 1)
        ((state r (inputWords s delta Q)).withPC (some (program k).entry))
        ((state rf w).withPC none) := by
  obtain ⟨t, rf, w, he, ho, ht⟩ := command_eval k r s delta Q
  refine ⟨rf, w, ho, t + 1, Nat.add_le_add_right ht 1, ?_⟩
  exact compiled_halt_trace he 0 14

theorem run_value_polynomial (k : ℕ) (r : Regs) (s delta Q : List Bool) :
    ∃ rf w, Output k s delta Q w ∧
      RunsIn (program k)
        (1000000 * (exponentValue delta Q + 1) ^ 2 *
          (inputWidth k s delta Q + 1) ^ 2 + 1)
        ((state r (inputWords s delta Q)).withPC (some (program k).entry))
        ((state rf w).withPC none) := by
  obtain ⟨rf, w, ho, hr⟩ := run_value k r s delta Q
  exact ⟨rf, w, ho, hr.mono (Nat.add_le_add_right (runtimeBound_polynomial k s delta Q) 1)⟩

theorem lifted_output {R S : ℕ} (k : ℕ) (r : Regs) (s delta Q : List Bool)
    (register : Fin 8 → Fin R) (stack : Fin 22 → Fin S)
    (frame : State R S) (hr : Function.Injective register)
    (hs : Function.Injective stack) :
    ∃ t rf w, t ≤ runtimeBound k s delta Q + 1 ∧ Output k s delta Q w ∧
      Eval (.call (ProgramLinking.liftProgram (program k) register stack)) t
        (embedState register stack frame (state r (inputWords s delta Q)))
        (embedState register stack frame (state rf w)) := by
  obtain ⟨rf, w, ho, t, ht, hrun⟩ := run_value k r s delta Q
  exact ⟨t, rf, w, ht, ho, eval_call_lifted (program k) register stack frame hr hs
    (a := state r (inputWords s delta Q)) (b := state rf w) hrun⟩

/-- The fixed compiler also realizes this multiword stage on a primitive tape.
Its input configuration is explicit so a caller can retain a larger frame. -/
theorem primitive_execution (k : ℕ) (r : Regs) (s delta Q : List Bool) :
    ∃ rf w, Output k s delta Q w ∧
      Computation.RunsIn (primitive (program k)).step
        (primitiveOverhead (program k) * (runtimeBound k s delta Q + 1))
        (primitiveCfg (program k)
          ((state r (inputWords s delta Q)).withPC (some (program k).entry)))
        (primitiveCfg (program k) ((state rf w).withPC none)) := by
  obtain ⟨rf, w, ho, hr⟩ := run_value k r s delta Q
  exact ⟨rf, w, ho, BitProgram.primitive_execution (program k) hr⟩

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
