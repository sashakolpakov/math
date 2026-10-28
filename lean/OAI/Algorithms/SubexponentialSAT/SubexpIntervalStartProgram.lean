import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIntervalFinishProgram
import OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open BitProgram StructuredCalls BinaryArithmetic
open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def initialState (regs : Regs) (r Q R : List Bool) : Data :=
  state regs (inputWords r Q R)

def finalState (regs : Regs) (r Q R output : List Bool) : Data :=
  state regs (Function.update (inputWords r Q R) 3 output)

def value (r Q R : ℕ) : ℕ := ((Q - 1) * (r - 1) - R * r) / (2 * r)

def subtractionPorts : Fin 8 → Fin 32 := ![6, 7, 9, 10, 11, 12, 13, 14]

theorem subtractionPorts_injective : Function.Injective subtractionPorts := by decide

private theorem embed_subtraction (frame regs : Regs) (w : Words) (word : List Bool) :
    embedState id subtractionPorts (state frame w)
      (SaturatingSubtractionProgram.state regs (w 6) (w 7) word) =
      state regs (Function.update w 9 word) := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · exact subtractionPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [ state, subtractionPorts]
  · intro i hi
    have h9 : i ≠ port 9 := by
      intro h
      exact hi ⟨2, h.symm⟩
    rw [← state_update frame regs w 9 word]
    simp only [Function.update_of_ne h9]

abbrev subtractionCmd : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram SaturatingSubtractionProgram.program id subtractionPorts)

theorem subtraction_eval (regs : Regs) (w : Words) (ho : w 9 = []) :
    ∃ (t : ℕ) (word : List Bool),
      Eval subtractionCmd t (state regs w)
        (state (fun _ => false) (Function.update w 9 word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w 6) - BinaryArithmetic.toNat (w 7) ∧
      word.length ≤ (w 6).length + (w 7).length ∧
      t ≤ 100 * ((w 6).length + (w 7).length + 1) := by
  obtain ⟨t, word, ht, he, hv, hl⟩ :=
    SaturatingSubtractionProgram.command_eval regs (w 6) (w 7)
  have hc := eval_call_lifted SaturatingSubtractionProgram.program id subtractionPorts
    (state regs w) Function.injective_id subtractionPorts_injective
    (compiled_halt_trace he 0 2)
  have hzero : Function.update w 9 [] = w := by
    rw [← ho]
    exact Function.update_eq_self _ _
  simp only [embed_subtraction, hzero] at hc
  exact ⟨t + 1, word, hc, hv, hl, ht⟩

abbrev command : Cmd 8 32 :=
  .seq SubexpIntervalCoreProgram.command
    (.seq subtractionCmd
      (.seq SubexpIntervalFinishProgram.divisionCmd SubexpIntervalFinishProgram.cleanup))

def program := compiled command (0 : Fin 32) 3

def runtimeBound (r Q R : List Bool) : ℕ := 10000 * (width r Q R)^2 + 1

theorem command_eval (regs : Regs) (r Q R : List Bool) (hr : 0 < BinaryArithmetic.toNat r) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval command t (initialState regs r Q R) (finalState rf r Q R word) ∧
      BinaryArithmetic.toNat word = value (BinaryArithmetic.toNat r) (BinaryArithmetic.toNat Q) (BinaryArithmetic.toNat R) ∧
      word.length ≤ 4 * width r Q R ∧ t ≤ 10000 * (width r Q R)^2 := by
  obtain ⟨t1, r1, w, he1, hw0, hw1, hw2, hw3, hw9, hv6, hv7, hv8, hwidth, ht1⟩ :=
    SubexpIntervalCoreProgram.command_eval regs r Q R
  obtain ⟨t2, num, he2, hvnum, hlnum, ht2⟩ := subtraction_eval r1 w hw9
  let w1 := Function.update w 9 num
  have hd : 0 < BinaryArithmetic.toNat (w1 8) := by simpa [w1, hv8] using Nat.mul_pos (by decide : 0 < 2) hr
  have ho : w1 3 = [] := by simpa [w1] using hw3
  obtain ⟨t3, r3, word, he3, hvword, hlword, ht3⟩ :=
    SubexpIntervalFinishProgram.division_eval (fun _ => false) w1 hd ho
  let w2 := Function.update w1 3 word
  have hnum : num.length ≤ 4 * width r Q R := by
    have h6 := hwidth 6
    have h7 := hwidth 7
    omega
  have hword : word.length ≤ 4 * width r Q R := by
    simpa only [w1, Function.update_self] using hlword.le.trans hnum
  have hw2bound : ∀ i, (w2 i).length ≤ 4 * width r Q R := by
    intro i
    by_cases h3 : i = 3
    · simpa [w2, h3] using hword
    by_cases h9 : i = 9
    · simpa [w2, w1, h9] using hnum
    have hi := hwidth i
    simpa [w2, w1, h3, h9] using hi.trans (by omega : 2 * width r Q R ≤ 4 * width r Q R)
  obtain ⟨t4, r4, he4, ht4⟩ := SubexpIntervalFinishProgram.cleanup_eval r3 w2 r Q R word
    (by simpa [w2, w1] using hw0) (by simpa [w2, w1] using hw1)
    (by simpa [w2, w1] using hw2) (by simp [w2]) (4 * width r Q R) hw2bound
  have he := he1.seq (he2.seq (he3.seq he4))
  refine ⟨t1 + (t2 + (t3 + t4)), r4, word, he, ?_, hword, ?_⟩
  · simpa [value, w1, hvnum, hv6, hv7, hv8] using hvword
  · let W := width r Q R
    have hW : 1 ≤ W := width_pos r Q R
    have hWsq : W ≤ W^2 := by nlinarith
    change t1 ≤ 1000 * W^2 at ht1
    change t4 ≤ 6 * (2 * (4 * W) + 3) at ht4
    have h6 := hwidth 6
    have h7 := hwidth 7
    have h8 := hwidth 8
    change (w 6).length ≤ 2 * W at h6
    change (w 7).length ≤ 2 * W at h7
    have hs : (w1 8).length + (w1 9).length + 1 ≤ 7 * W := by
      simp only [w1, Function.update_self,
        Function.update_of_ne (by decide : (8 : Fin 10) ≠ 9)]
      omega
    have hp := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hs 2)
    have h8' : (w1 8).length ≤ 2 * W := by simpa [w1] using h8
    have h9' : (w1 9).length ≤ 4 * W := by simpa [w1] using hnum
    change _ ≤ 10000 * W^2
    nlinarith only [ht1, ht2, ht3, ht4, hp, h8', h9', h6, h7, hW, hWsq]

theorem run (regs : Regs) (r Q R : List Bool) (hr : 0 < BinaryArithmetic.toNat r) :
    ∃ (rf : Regs) (word : List Bool),
      BitProgram.RunsIn program (runtimeBound r Q R)
        ((initialState regs r Q R).withPC (some program.entry))
        ((finalState rf r Q R word).withPC none) ∧
      BinaryArithmetic.toNat word = value (BinaryArithmetic.toNat r) (BinaryArithmetic.toNat Q) (BinaryArithmetic.toNat R) ∧
      word.length ≤ 4 * width r Q R := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ := command_eval regs r Q R hr
  exact ⟨rf, word, ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 3⟩, hv, hl⟩

theorem finalState_wordBound (regs : Regs) (r Q R word : List Bool)
    (hw : word.length ≤ 4 * width r Q R) :
    ∀ i, ((finalState regs r Q R word).stacks i).length ≤ 4 * width r Q R := by
  intro i
  fin_cases i <;> simp [finalState, state, inputWords]
  all_goals dsimp [width] at *; omega

/-- Public initializer interface, including every final physical word's size. -/
theorem run_value (regs : Regs) (r Q R : List Bool) (hr : 0 < BinaryArithmetic.toNat r) :
    ∃ d : Data,
      BitProgram.RunsIn program (runtimeBound r Q R)
        ((initialState regs r Q R).withPC (some program.entry)) (d.withPC none) ∧
      d.stacks 0 = r ∧ d.stacks 1 = Q ∧ d.stacks 2 = R ∧
      BinaryArithmetic.toNat (d.stacks 3) = value (BinaryArithmetic.toNat r) (BinaryArithmetic.toNat Q) (BinaryArithmetic.toNat R) ∧
      (∀ i, 4 ≤ i.val → d.stacks i = []) ∧
      (∀ i, (d.stacks i).length ≤ 4 * width r Q R) := by
  obtain ⟨rf, word, he, hv, hl⟩ := run regs r Q R hr
  refine ⟨finalState rf r Q R word, he, rfl, rfl, rfl, hv, ?_,
    finalState_wordBound rf r Q R word hl⟩
  intro i hi
  fin_cases i <;> simp_all [finalState, state, inputWords]

theorem primitive_run (regs : Regs) (r Q R : List Bool) (hr : 0 < BinaryArithmetic.toNat r) :
    ∃ (rf : Regs) (word : List Bool),
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound r Q R)
        (BitProgram.primitiveCfg program ((initialState regs r Q R).withPC (some program.entry)))
        (BitProgram.primitiveCfg program ((finalState rf r Q R word).withPC none)) ∧
      BinaryArithmetic.toNat word = value (BinaryArithmetic.toNat r) (BinaryArithmetic.toNat Q) (BinaryArithmetic.toNat R) := by
  obtain ⟨rf, word, he, hv, _⟩ := run regs r Q R hr
  exact ⟨rf, word, BitProgram.primitive_execution program he, hv⟩

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
