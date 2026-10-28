import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport

namespace OAI.Algorithms

/-!
# A source-preserving incidence-degree parameter program

Local stacks 0 and 1 hold binary `u` and `B`; stack 2 receives `1 + u * B`.
Stacks 3 and 4 hold a physically loaded one and a product, then are cleared.
The five arithmetic work stacks are 5 through 9. All instructions and port maps
are fixed independently of the input words.
-/

namespace SubexponentialSAT.SubexpIncidenceGuardProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := StructuredProgram.State 8 10

def work : Fin 5 ↪ Fin 10 where
  toFun i := ⟨5 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem work_ne_low (i j : Fin 5) : work i ≠ Fin.castAdd 5 j := by
  intro h
  have hv := congrArg Fin.val h
  change 5 + i.val = j.val at hv
  have hj := j.isLt
  omega

@[simp] theorem work_ne_two (i : Fin 5) : work i ≠ 2 := work_ne_low i 2
@[simp] theorem work_ne_three (i : Fin 5) : work i ≠ 3 := work_ne_low i 3
@[simp] theorem work_ne_four (i : Fin 5) : work i ≠ 4 := work_ne_low i 4

def arithmeticPorts (a b o : Fin 5) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 10 where
  left := Fin.castAdd 5 a
  right := Fin.castAdd 5 b
  out := Fin.castAdd 5 o
  work := work
  out_ne_left := by
    intro h
    exact hoa (Fin.ext (congrArg (fun i : Fin 10 => i.val) h))
  out_ne_right := by
    intro h
    exact hob (Fin.ext (congrArg (fun i : Fin 10 => i.val) h))
  work_ne_left := fun i => work_ne_low i a
  work_ne_right := fun i => work_ne_low i b
  work_ne_out := fun i => work_ne_low i o

def productPorts : ArithmeticCalls.Ports 10 :=
  arithmeticPorts 0 1 4 (by decide) (by decide)

def sumPorts : ArithmeticCalls.Ports 10 :=
  arithmeticPorts 3 4 2 (by decide) (by decide)

/-- The source words are arbitrary, including leading zeroes. -/
def Ready (d : Data) : Prop := ∀ i : Fin 10, 2 ≤ i.val → d.stacks i = []

theorem ready_work {d : Data} (h : Ready d) (i : Fin 5) : d.stacks (work i) = [] :=
  h (work i) (by change 2 ≤ 5 + i.val; omega)

abbrev command : Cmd 8 10 :=
  .seq (ArithmeticExpressionSupport.pushWord 3 [true])
    (.seq (ArithmeticCalls.multiplyAt productPorts)
      (.seq (ArithmeticCalls.addAt sumPorts)
        (.seq (ArithmeticExpressionSupport.clearCmd 3)
          (ArithmeticExpressionSupport.clearCmd 4))))

def width (d : Data) : ℕ := (d.stacks 0).length + (d.stacks 1).length + 3

theorem width_pos (d : Data) : 0 < width d := by unfold width; omega

private theorem total_cost_bound {tm ta L W : ℕ}
    (hm : tm ≤ 100 * W ^ 2) (ha : ta ≤ 100 * W ^ 2)
    (hW : 3 ≤ W) (hL : L + 2 ≤ W) :
    2 + (tm + (ta + (5 + (2 * L + 3)))) ≤ 300 * W ^ 2 := by
  nlinarith

/-- An actual execution with exact numeric output, source preservation,
cleared work storage, a linear word bound, and quadratic instruction cost. -/
theorem command_eval (d : Data) (hd : Ready d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Eval command t d ⟨rf, Function.update d.stacks 2 word⟩ ∧
      BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      word.length ≤ width d ∧ t ≤ 300 * width d ^ 2 := by
  have hd2 := hd 2 (by decide)
  have hd3 := hd 3 (by decide)
  have hd4 := hd 4 (by decide)
  obtain ⟨r1, hload⟩ := ArithmeticExpressionSupport.pushWord_eval 3 [true] d
  let d1 : Data := ⟨r1, Function.update d.stacks 3 [true]⟩
  have hload' : Eval (ArithmeticExpressionSupport.pushWord 3 [true]) 2 d d1 := by
    simpa only [hd3, List.append_nil, List.length_cons, List.length_nil] using hload
  have hmReady : ArithmeticCalls.Valid productPorts d1 := by
    constructor
    · simpa [productPorts, arithmeticPorts, d1] using hd4
    · intro i
      simpa [productPorts, arithmeticPorts, d1] using ready_work hd i
  obtain ⟨tm, r2, prod, hm, hprod, hlprod, htm⟩ :=
    ArithmeticCalls.multiplyAt_eval productPorts d1 hmReady
  simp only [productPorts, arithmeticPorts] at hm hprod hlprod htm
  let d2 : Data := ⟨r2, Function.update d1.stacks 4 prod⟩
  have hm' : Eval (ArithmeticCalls.multiplyAt productPorts) tm d1 d2 := hm
  have hprod' : BinaryArithmetic.toNat prod = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) := by
    simpa [d1] using hprod
  have hlprod' : prod.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := by
    simpa [d1] using hlprod
  have htm' : tm ≤ 100 * ((d.stacks 0).length + (d.stacks 1).length + 1) ^ 2 := by
    simpa [d1] using htm
  have haReady : ArithmeticCalls.Valid sumPorts d2 := by
    constructor
    · simpa [sumPorts, arithmeticPorts, d2, d1] using hd2
    · intro i
      simpa [sumPorts, arithmeticPorts, d2, d1] using ready_work hd i
  obtain ⟨ta, r3, word, ha, hvword, hlword, hta⟩ :=
    ArithmeticCalls.addAt_eval sumPorts d2 haReady
  simp only [sumPorts, arithmeticPorts] at ha hvword hlword hta
  let d3 : Data := ⟨r3, Function.update d2.stacks 2 word⟩
  have ha' : Eval (ArithmeticCalls.addAt sumPorts) ta d2 d3 := ha
  have hvword' : BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat prod := by
    simpa [d2, d1] using hvword
  have hlword' : word.length ≤ prod.length + 2 := by
    simpa [d2, d1, Nat.add_comm, Nat.add_left_comm] using hlword
  have hta' : ta ≤ 100 * (prod.length + 2) ^ 2 := by
    simpa [d2, d1, Nat.add_comm, Nat.add_left_comm] using hta
  let d4 : Data := ⟨readRegs d3.regs 0 1 none, Function.update d3.stacks 3 []⟩
  have hclear1 : Eval (ArithmeticExpressionSupport.clearCmd 3) 5 d3 d4 := by
    simpa [d3, d2, d1] using ArithmeticExpressionSupport.clear_eval 3 d3
  let d5 : Data := ⟨readRegs d4.regs 0 1 none, Function.update d4.stacks 4 []⟩
  have hclearProd : Eval (ArithmeticExpressionSupport.clearCmd 4)
      (2 * prod.length + 3) d4 d5 := by
    simpa [d4, d3, d2] using ArithmeticExpressionSupport.clear_eval 4 d4
  have hfinal : d5 = (⟨d5.regs, Function.update d.stacks 2 word⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk d5.regs)
    funext i
    by_cases h2 : i = 2
    · subst i; simp [d4, d3, d2, d1]
    by_cases h3 : i = 3
    · subst i; simp [d4, d3, d2, d1, hd3]
    by_cases h4 : i = 4
    · subst i; simp [d4, d3, d2, d1, hd4]
    · simp [d4, d3, d2, d1, h2, h3, h4]
  have he := hload'.seq (hm'.seq (ha'.seq (hclear1.seq hclearProd)))
  rw [hfinal] at he
  refine ⟨2 + (tm + (ta + (5 + (2 * prod.length + 3)))), d5.regs, word,
    he, ?_, ?_, ?_⟩
  · rw [hvword', hprod']
  · unfold width; omega
  · have hmBound : tm ≤ 100 * width d ^ 2 := htm'.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold width; omega) _))
    have haBound : ta ≤ 100 * width d ^ 2 := hta'.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold width; omega) _))
    have hw : 3 ≤ width d := by unfold width; omega
    have hpw : prod.length + 2 ≤ width d := by unfold width; omega
    exact total_cost_bound hmBound haBound hw hpw

def program := StructuredCalls.compiled command 0 2

theorem command_trace (d : Data) (hd : Ready d) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (word : List Bool),
      Trace program (t + 1) (d.withPC (some program.entry))
        ((⟨rf, Function.update d.stacks 2 word⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      word.length ≤ width d ∧ t ≤ 300 * width d ^ 2 := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ := command_eval d hd
  exact ⟨t, rf, word, StructuredCalls.compiled_halt_trace he 0 2, hv, hl, ht⟩

theorem command_primitive (d : Data) (hd : Ready d) :
    ∃ (rf : Fin 8 → Bool) (word : List Bool),
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * (300 * width d ^ 2 + 1))
        (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((⟨rf, Function.update d.stacks 2 word⟩ : Data).withPC none)) ∧
      BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      word.length ≤ width d := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ := command_eval d hd
  refine ⟨rf, word, ?_, hv, hl⟩
  exact (StructuredCalls.primitive_execution he 0 2).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 1))

/-- The returned natural number is positive, as needed by the field helper. -/
theorem output_pos {d : Data} {word : List Bool}
    (h : BinaryArithmetic.toNat word = 1 + BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1)) :
    0 < BinaryArithmetic.toNat word := by omega

end SubexponentialSAT.SubexpIncidenceGuardProgram

end OAI.Algorithms
