import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport

namespace OAI.Algorithms

/-!
# Actual arithmetic operands for the tail guard

Inputs R,Q,delta,s occupy local stacks 0,1,2,3. Outputs R² and
16*Q*delta*s occupy stacks 4 and 5. Stacks 6,7,8 are temporary words and
9 through 13 are arithmetic work. The sources are preserved and every
temporary word is cleared. The constant sixteen is loaded by bit instructions.
-/

namespace SubexponentialSAT.SubexpGuardTailProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := StructuredProgram.State 8 14

def work : Fin 5 ↪ Fin 14 where
  toFun i := ⟨9 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem work_ne_low (i : Fin 5) (j : Fin 9) : work i ≠ Fin.castAdd 5 j := by
  intro h
  have hv := congrArg Fin.val h
  change 9 + i.val = j.val at hv
  have hj := j.isLt
  omega

@[simp] theorem work_ne_four (i : Fin 5) : work i ≠ 4 := work_ne_low i 4
@[simp] theorem work_ne_five (i : Fin 5) : work i ≠ 5 := work_ne_low i 5
@[simp] theorem work_ne_six (i : Fin 5) : work i ≠ 6 := work_ne_low i 6
@[simp] theorem work_ne_seven (i : Fin 5) : work i ≠ 7 := work_ne_low i 7
@[simp] theorem work_ne_eight (i : Fin 5) : work i ≠ 8 := work_ne_low i 8

def ports (a b o : Fin 9) (hoa : o ≠ a) (hob : o ≠ b) : ArithmeticCalls.Ports 14 where
  left := Fin.castAdd 5 a
  right := Fin.castAdd 5 b
  out := Fin.castAdd 5 o
  work := work
  out_ne_left := by
    intro h
    exact hoa (Fin.ext (congrArg (fun i : Fin 14 => i.val) h))
  out_ne_right := by
    intro h
    exact hob (Fin.ext (congrArg (fun i : Fin 14 => i.val) h))
  work_ne_left := fun i => work_ne_low i a
  work_ne_right := fun i => work_ne_low i b
  work_ne_out := fun i => work_ne_low i o

def squarePorts := ports 0 0 4 (by decide) (by decide)
def pairPorts := ports 1 2 7 (by decide) (by decide)
def triplePorts := ports 7 3 8 (by decide) (by decide)
def scalePorts := ports 6 8 5 (by decide) (by decide)

def Ready (d : Data) : Prop := ∀ i : Fin 14, 4 ≤ i.val → d.stacks i = []

theorem ready_work {d : Data} (h : Ready d) (i : Fin 5) : d.stacks (work i) = [] :=
  h (work i) (by change 4 ≤ 9 + i.val; omega)

def sixteen : List Bool := [false, false, false, false, true]

@[simp] theorem sixteen_value : BinaryArithmetic.toNat sixteen = 16 := rfl
@[simp] theorem sixteen_length : sixteen.length = 5 := rfl

abbrev command : Cmd 8 14 :=
  .seq (ArithmeticExpressionSupport.pushWord 6 sixteen)
    (.seq (ArithmeticCalls.multiplyAt squarePorts)
      (.seq (ArithmeticCalls.multiplyAt pairPorts)
        (.seq (ArithmeticCalls.multiplyAt triplePorts)
          (.seq (ArithmeticCalls.multiplyAt scalePorts)
            (.seq (ArithmeticExpressionSupport.clearCmd 6)
              (.seq (ArithmeticExpressionSupport.clearCmd 7)
                (ArithmeticExpressionSupport.clearCmd 8)))))))

def width (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length + 8

private theorem time_mono {t l W : ℕ} (ht : t ≤ 100 * l ^ 2) (hl : l ≤ 2 * W) :
    t ≤ 400 * W ^ 2 := by
  calc
    t ≤ 100 * (2 * W) ^ 2 := ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _))
    _ = 400 * W ^ 2 := by ring

private theorem total_cost_bound {t1 t2 t3 t4 A B W : ℕ}
    (h1 : t1 ≤ 400 * W ^ 2) (h2 : t2 ≤ 400 * W ^ 2)
    (h3 : t3 ≤ 400 * W ^ 2) (h4 : t4 ≤ 400 * W ^ 2)
    (hW : 8 ≤ W) (hA : A ≤ W) (hB : B ≤ W) :
    10 + (t1 + (t2 + (t3 + (t4 + (13 + ((2 * A + 3) + (2 * B + 3))))))) ≤
      2000 * W ^ 2 := by
  nlinarith

/-- Four actual multiplications produce both guard operands. The post-state
changes only the two output stacks, and the runtime is polynomial in input width. -/
theorem command_eval (d : Data) (hd : Ready d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (square tail : List Bool),
      Eval command t d
        ⟨rf, Function.update (Function.update d.stacks 4 square) 5 tail⟩ ∧
      BinaryArithmetic.toNat square = BinaryArithmetic.toNat (d.stacks 0) ^ 2 ∧
      BinaryArithmetic.toNat tail = 16 * BinaryArithmetic.toNat (d.stacks 1) * BinaryArithmetic.toNat (d.stacks 2) * BinaryArithmetic.toNat (d.stacks 3) ∧
      square.length ≤ 2 * (d.stacks 0).length + 1 ∧
      tail.length ≤ (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length + 8 ∧
      t ≤ 2000 * width d ^ 2 := by
  have hd4 := hd 4 (by decide)
  have hd5 := hd 5 (by decide)
  have hd6 := hd 6 (by decide)
  have hd7 := hd 7 (by decide)
  have hd8 := hd 8 (by decide)
  obtain ⟨r1, hload⟩ := ArithmeticExpressionSupport.pushWord_eval 6 sixteen d
  let d1 : Data := ⟨r1, Function.update d.stacks 6 sixteen⟩
  have hload' : Eval (ArithmeticExpressionSupport.pushWord 6 sixteen) 10 d d1 := by
    simpa only [hd6, List.append_nil, sixteen_length] using hload
  have hready1 : ArithmeticCalls.Valid squarePorts d1 := by
    constructor
    · simpa [squarePorts, ports, d1] using hd4
    · intro i; simpa [squarePorts, ports, d1] using ready_work hd i
  obtain ⟨t1, r2, square, h1, hv1, hl1, ht1⟩ :=
    ArithmeticCalls.multiplyAt_eval squarePorts d1 hready1
  let d2 : Data := ⟨r2, Function.update d1.stacks 4 square⟩
  have h1' : Eval (ArithmeticCalls.multiplyAt squarePorts) t1 d1 d2 := h1
  have hvSquare : BinaryArithmetic.toNat square = BinaryArithmetic.toNat (d.stacks 0) ^ 2 := by
    simpa [squarePorts, ports, d1, pow_two] using hv1
  have hlSquare : square.length ≤ 2 * (d.stacks 0).length + 1 := by
    simpa [squarePorts, ports, d1, two_mul] using hl1
  have htSquare : t1 ≤ 100 * (2 * (d.stacks 0).length + 1) ^ 2 := by
    simpa [squarePorts, ports, d1, two_mul] using ht1
  have hready2 : ArithmeticCalls.Valid pairPorts d2 := by
    constructor
    · simpa [pairPorts, ports, d2, d1] using hd7
    · intro i; simpa [pairPorts, ports, d2, d1] using ready_work hd i
  obtain ⟨t2, r3, pair, h2, hv2, hl2, ht2⟩ :=
    ArithmeticCalls.multiplyAt_eval pairPorts d2 hready2
  let d3 : Data := ⟨r3, Function.update d2.stacks 7 pair⟩
  have h2' : Eval (ArithmeticCalls.multiplyAt pairPorts) t2 d2 d3 := h2
  have hvPair : BinaryArithmetic.toNat pair = BinaryArithmetic.toNat (d.stacks 1) * BinaryArithmetic.toNat (d.stacks 2) := by
    simpa [pairPorts, ports, d2, d1] using hv2
  have hlPair : pair.length ≤ (d.stacks 1).length + (d.stacks 2).length + 1 := by
    simpa [pairPorts, ports, d2, d1] using hl2
  have htPair : t2 ≤ 100 * ((d.stacks 1).length + (d.stacks 2).length + 1) ^ 2 := by
    simpa [pairPorts, ports, d2, d1] using ht2
  have hready3 : ArithmeticCalls.Valid triplePorts d3 := by
    constructor
    · simpa [triplePorts, ports, d3, d2, d1] using hd8
    · intro i; simpa [triplePorts, ports, d3, d2, d1] using ready_work hd i
  obtain ⟨t3, r4, triple, h3, hv3, hl3, ht3⟩ :=
    ArithmeticCalls.multiplyAt_eval triplePorts d3 hready3
  let d4 : Data := ⟨r4, Function.update d3.stacks 8 triple⟩
  have h3' : Eval (ArithmeticCalls.multiplyAt triplePorts) t3 d3 d4 := h3
  have hvTriple : BinaryArithmetic.toNat triple = BinaryArithmetic.toNat pair * BinaryArithmetic.toNat (d.stacks 3) := by
    simpa [triplePorts, ports, d3, d2, d1] using hv3
  have hlTriple : triple.length ≤ pair.length + (d.stacks 3).length + 1 := by
    simpa [triplePorts, ports, d3, d2, d1] using hl3
  have htTriple : t3 ≤ 100 * (pair.length + (d.stacks 3).length + 1) ^ 2 := by
    simpa [triplePorts, ports, d3, d2, d1] using ht3
  have hready4 : ArithmeticCalls.Valid scalePorts d4 := by
    constructor
    · simpa [scalePorts, ports, d4, d3, d2, d1] using hd5
    · intro i; simpa [scalePorts, ports, d4, d3, d2, d1] using ready_work hd i
  obtain ⟨t4, r5, tail, h4, hv4, hl4, ht4⟩ :=
    ArithmeticCalls.multiplyAt_eval scalePorts d4 hready4
  let d5 : Data := ⟨r5, Function.update d4.stacks 5 tail⟩
  have h4' : Eval (ArithmeticCalls.multiplyAt scalePorts) t4 d4 d5 := h4
  have hvTail : BinaryArithmetic.toNat tail = 16 * BinaryArithmetic.toNat triple := by
    simpa [scalePorts, ports, d4, d3, d2, d1] using hv4
  have hlTail : tail.length ≤ triple.length + 6 := by
    simpa [scalePorts, ports, d4, d3, d2, d1, Nat.add_comm, Nat.add_left_comm] using hl4
  have htTail : t4 ≤ 100 * (triple.length + 6) ^ 2 := by
    simpa [scalePorts, ports, d4, d3, d2, d1, Nat.add_comm, Nat.add_left_comm] using ht4
  let d6 : Data := ⟨readRegs d5.regs 0 1 none, Function.update d5.stacks 6 []⟩
  have hc1 : Eval (ArithmeticExpressionSupport.clearCmd 6) 13 d5 d6 := by
    simpa [d5, d4, d3, d2, d1] using ArithmeticExpressionSupport.clear_eval 6 d5
  let d7 : Data := ⟨readRegs d6.regs 0 1 none, Function.update d6.stacks 7 []⟩
  have hc2 : Eval (ArithmeticExpressionSupport.clearCmd 7) (2 * pair.length + 3) d6 d7 := by
    simpa [d6, d5, d4, d3] using ArithmeticExpressionSupport.clear_eval 7 d6
  let d8 : Data := ⟨readRegs d7.regs 0 1 none, Function.update d7.stacks 8 []⟩
  have hc3 : Eval (ArithmeticExpressionSupport.clearCmd 8) (2 * triple.length + 3) d7 d8 := by
    simpa [d7, d6, d5, d4] using ArithmeticExpressionSupport.clear_eval 8 d7
  have hfinal : d8 =
      (⟨d8.regs, Function.update (Function.update d.stacks 4 square) 5 tail⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk d8.regs)
    funext i
    by_cases h4 : i = 4
    · subst i; simp [d7, d6, d5, d4, d3, d2, d1]
    by_cases h5 : i = 5
    · subst i; simp [d7, d6, d5, d4, d3, d2, d1]
    by_cases h6 : i = 6
    · subst i; simp [d7, d6, d5, d4, d3, d2, d1, hd6]
    by_cases h7 : i = 7
    · subst i; simp [d7, d6, d5, d4, d3, d2, d1, hd7]
    by_cases h8 : i = 8
    · subst i; simp [d7, d6, d5, d4, d3, d2, d1, hd8]
    · simp [d7, d6, d5, d4, d3, d2, d1, h4, h5, h6, h7, h8]
  have he := hload'.seq (h1'.seq (h2'.seq (h3'.seq (h4'.seq (hc1.seq (hc2.seq hc3))))))
  rw [hfinal] at he
  refine ⟨10 + (t1 + (t2 + (t3 + (t4 + (13 + ((2 * pair.length + 3) +
    (2 * triple.length + 3))))))), d8.regs, square, tail, he, hvSquare, ?_, hlSquare, ?_, ?_⟩
  · rw [hvTail, hvTriple, hvPair]
    ring
  · omega
  · have hT1 := time_mono htSquare (W := width d) (by unfold width; omega)
    have hT2 := time_mono htPair (W := width d) (by unfold width; omega)
    have hT3 := time_mono htTriple (W := width d) (by unfold width; omega)
    have hT4 := time_mono htTail (W := width d) (by unfold width; omega)
    have hW : 8 ≤ width d := by unfold width; omega
    have hP : pair.length ≤ width d := by unfold width; omega
    have hT : triple.length ≤ width d := by unfold width; omega
    exact total_cost_bound hT1 hT2 hT3 hT4 hW hP hT

def program := StructuredCalls.compiled command 0 4

theorem command_trace (d : Data) (hd : Ready d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (square tail : List Bool),
      Trace program (t + 1) (d.withPC (some program.entry))
        ((⟨rf, Function.update (Function.update d.stacks 4 square) 5 tail⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat square = BinaryArithmetic.toNat (d.stacks 0) ^ 2 ∧
      BinaryArithmetic.toNat tail = 16 * BinaryArithmetic.toNat (d.stacks 1) * BinaryArithmetic.toNat (d.stacks 2) * BinaryArithmetic.toNat (d.stacks 3) ∧
      square.length ≤ 2 * (d.stacks 0).length + 1 ∧
      tail.length ≤ (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length + 8 ∧
      t ≤ 2000 * width d ^ 2 := by
  obtain ⟨t, rf, square, tail, he, hv1, hv2, hl1, hl2, ht⟩ := command_eval d hd
  exact ⟨t, rf, square, tail, StructuredCalls.compiled_halt_trace he 0 4,
    hv1, hv2, hl1, hl2, ht⟩

theorem command_primitive (d : Data) (hd : Ready d) :
    ∃ (rf : Fin 8 → Bool) (square tail : List Bool),
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * (2000 * width d ^ 2 + 1))
        (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((⟨rf, Function.update (Function.update d.stacks 4 square) 5 tail⟩ : Data).withPC none)) ∧
      BinaryArithmetic.toNat square = BinaryArithmetic.toNat (d.stacks 0) ^ 2 ∧
      BinaryArithmetic.toNat tail = 16 * BinaryArithmetic.toNat (d.stacks 1) * BinaryArithmetic.toNat (d.stacks 2) * BinaryArithmetic.toNat (d.stacks 3) ∧
      square.length ≤ 2 * (d.stacks 0).length + 1 ∧
      tail.length ≤ (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length + 8 := by
  obtain ⟨t, rf, square, tail, he, hv1, hv2, hl1, hl2, ht⟩ := command_eval d hd
  refine ⟨rf, square, tail, ?_, hv1, hv2, hl1, hl2⟩
  exact (StructuredCalls.primitive_execution he 0 4).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 1))

end SubexponentialSAT.SubexpGuardTailProgram

end OAI.Algorithms
