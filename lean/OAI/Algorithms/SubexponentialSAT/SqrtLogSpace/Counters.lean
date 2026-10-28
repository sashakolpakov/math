import OAI.Algorithms.SubexponentialSAT.CounterWidth
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import Mathlib.Data.Nat.Size

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

/-- Fixed-width words and their in-range numeric indices are equivalent.
This specification is not a retained list of the enumerated words. -/
def wordEquiv (width : ℕ) : Fin (2 ^ width) ≃ {xs : List Bool // xs.length = width} where
  toFun i := ⟨ExecCNFTupleEnumeration.fixedBits width i, by simp⟩
  invFun xs := ⟨value xs.val, by
    simpa only [xs.property] using ExecCNFTupleOdometer.value_lt_power_length xs.val⟩
  left_inv i := Fin.ext (ExecCNFTupleEnumeration.fixedBits_value width i i.isLt)
  right_inv xs := Subtype.ext (ExecCNFTupleEnumeration.word_eq_of_length_value
    (by simp only [ExecCNFTupleEnumeration.fixedBits_length, xs.property])
    (ExecCNFTupleEnumeration.fixedBits_value width (value xs.val)
      (by simpa only [xs.property] using ExecCNFTupleOdometer.value_lt_power_length xs.val)))

/-- The binary word of an exponentially large fuel has only linear width. -/
theorem fuel_bits_length (width : ℕ) : (2 ^ width).bits.length = width + 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_pow]

/-- The canonical binary encoding of a number at most the assignment count is short. -/
theorem bits_length_le_of_le_pow {n width : ℕ} (h : n ≤ 2 ^ width) :
    n.bits.length ≤ width + 1 := by
  rw [Nat.size_eq_bits_len, ← Nat.size_pow]
  exact Nat.size_le_size h

/-- The actual ripple increment remains the next fixed-width word before overflow. -/
theorem increment_word {width : ℕ} (i : Fin (2 ^ width)) (h : i.val + 1 < 2 ^ width) :
    ripple true (wordEquiv width i).val = (wordEquiv width ⟨i.val + 1, h⟩).val := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · apply Nat.le_antisymm
    · exact (increment_length_le_of_lt (wordEquiv width i).val width
        (wordEquiv width i).property.le (by simpa [wordEquiv,
          ExecCNFTupleEnumeration.fixedBits_value width i i.isLt] using h)).trans_eq
          (wordEquiv width ⟨i.val + 1, h⟩).property.symm
    · have hlen : (wordEquiv width i).val.length ≤
          (ripple true (wordEquiv width i).val).length := by
        generalize (wordEquiv width i).val = xs
        induction xs with
        | nil => simp
        | cons b xs ih =>
            cases b
            · simp [ripple]
            · simp only [ripple, ↓reduceIte, Bool.not_true, List.length_cons] at *
              omega
      simpa only [(wordEquiv width i).property,
        (wordEquiv width ⟨i.val + 1, h⟩).property] using hlen
  · simp [wordEquiv, value_increment, ExecCNFTupleEnumeration.fixedBits_value, i.isLt, h]

/-- The local routine is linear in the current word, even when its value is exponential. -/
theorem ripple_prefix_stack_bound (carry bit present flag : Bool) (word : List Bool)
    {steps : ℕ} {intermediate : Cfg 3 2 11}
    (hle : steps ≤ rippleCost carry word + 1)
    (htrace : Trace (rippleProgram carry) steps
      ((localData bit present flag word []).withPC (some (rippleProgram carry).entry))
      intermediate) (i : Fin 2) :
    (intermediate.stacks i).length ≤ 9 * word.length + 8 := by
  have hs : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hg := trace_dataBits (rippleProgram carry) htrace
  have hc := rippleCost_le carry word
  have hinit : dataBits
      ((localData bit present flag word []).withPC (some (rippleProgram carry).entry)) =
      word.length := by
    simp [dataBits, stackBits, localData,
      counterStacks, Fin.sum_univ_two]
  rw [hinit] at hg
  omega

/-- Generic actual increment call on the same finite ports as countdown. -/
def incrementCmd {R S : ℕ} (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram true) p.register (stackPorts p))

noncomputable def incrementResult {R S : ℕ} (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (d.regs (p.register 2)) (ripple true (d.stacks p.counter)) []

theorem increment_eval {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (incrementCmd p) (rippleCost true (d.stacks p.counter) + 1)
      d (incrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram true) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace true (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (incrementCmd p) _
    (install p d _ _ _ _ []) (incrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

@[simp] theorem incrementResult_counter {R S : ℕ} (p : Ports R S) (d : Data R S) :
    (incrementResult p d).stacks p.counter = ripple true (d.stacks p.counter) :=
  install_counter p d _ _ _ _ _

@[simp] theorem incrementResult_scratch {R S : ℕ} (p : Ports R S) (d : Data R S) :
    (incrementResult p d).stacks p.scratch = [] := install_scratch p d _ _ _ _ _

/-- Every off-counter caller stack is preserved, including cleared scratch. -/
theorem incrementResult_stacks {R S : ℕ} (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    (incrementResult p d).stacks =
      Function.update d.stacks p.counter (ripple true (d.stacks p.counter)) := by
  funext i
  by_cases hc : i = p.counter
  · subst i
    simp
  · by_cases hi : i = p.scratch
    · subst i
      simp [hc, hs]
    · rw [Function.update_of_ne hc]
      exact install_other_stack p d _ _ _ _ _ i hc hi

theorem incrementResult_register_frame {R S : ℕ} (p : Ports R S) (d : Data R S)
    (i : Fin R) (hi : ¬ ∃ j, p.register j = i) :
    (incrementResult p d).regs i = d.regs i :=
  StructuredCalls.embedState_register_frame _ _ _ _ i hi

/-- Consume a length witness and construct the binary fuel `2^h` by pushing
one zero per witness bit. The finite control never stores `h` or `2^h`. -/
def powerTwoProgram : Program 3 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 true 1
    | 1 => .push 1 0 2
    | 2 => .pop 0 0 1 3
    | 3 => .branch 1 4 6
    | 4 => .set 0 false 5
    | 5 => .push 1 0 2
    | _ => .halt

private theorem powerTwo_scan (word output : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 2)
      (counterCfg 2 bit present flag word output)
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ output)) := by
  induction word generalizing output bit present with
  | nil =>
      exact .cons (b := counterCfg 3 false false flag [] output)
        (by simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  | cons b word ih =>
      have h := Computation.Trace.cons
        (show step powerTwoProgram (counterCfg 2 bit present flag (b :: word) output) =
          some (counterCfg 3 b true flag word output) by
            simp [step, powerTwoProgram, counterCfg, execInstr, readRegs])
        (Computation.Trace.cons
          (show step powerTwoProgram (counterCfg 3 b true flag word output) =
            some (counterCfg 4 b true flag word output) by
              simp [step, powerTwoProgram, counterCfg, execInstr])
          (Computation.Trace.cons
            (show step powerTwoProgram (counterCfg 4 b true flag word output) =
              some (counterCfg 5 false true flag word output) by
                simp [step, powerTwoProgram, counterCfg, execInstr])
            (Computation.Trace.cons
              (show step powerTwoProgram (counterCfg 5 false true flag word output) =
                some (counterCfg 2 false true flag word (false :: output)) by
                  simp [step, powerTwoProgram, counterCfg, execInstr])
              (ih (false :: output) false true))))
      convert h using 1
      simp [List.replicate_succ', List.append_assoc]

theorem powerTwo_trace (word : List Bool) (bit present flag : Bool) :
    Trace powerTwoProgram (4 * word.length + 5)
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry))
      ((localData false false flag []
        (List.replicate word.length false ++ [true])).withPC none) := by
  have hstart : Trace powerTwoProgram 2 (counterCfg 0 bit present flag word [])
      (counterCfg 2 true present flag word [true]) :=
    .cons (b := counterCfg 1 true present flag word [])
      (by simp [step, powerTwoProgram, counterCfg, execInstr])
      (.cons (by simp [step, powerTwoProgram, counterCfg, execInstr]) (.refl _))
  have hend : Trace powerTwoProgram 1
      (counterCfg 6 false false flag [] (List.replicate word.length false ++ [true]))
      ((localData false false flag [] (List.replicate word.length false ++ [true])).withPC none) :=
    .cons (by simp [step, powerTwoProgram, counterCfg, execInstr, localData,
      StructuredProgram.State.withPC]) (.refl _)
  have h := (hstart.trans (powerTwo_scan word [true] true present flag)).trans hend
  have ht : 2 + (4 * word.length + 2) + 1 = 4 * word.length + 5 := by omega
  rw [ht] at h
  simpa [localData, StructuredProgram.State.withPC, counterCfg, powerTwoProgram] using h

theorem powerTwo_value (width : ℕ) :
    value (List.replicate width false ++ [true]) = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

/-- Every prefix of fuel construction has linear storage, including scratch. -/
theorem powerTwo_prefix_stack_bound (word : List Bool) (bit present flag : Bool)
    {steps : ℕ} {intermediate : Cfg 3 2 7} (hle : steps ≤ 4 * word.length + 5)
    (htrace : Trace powerTwoProgram steps
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry)) intermediate)
    (i : Fin 2) : (intermediate.stacks i).length ≤ 5 * word.length + 5 := by
  have hs : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have hg := trace_dataBits powerTwoProgram htrace
  have hinit : dataBits
      ((localData bit present flag word []).withPC (some powerTwoProgram.entry)) = word.length := by
    simp [dataBits, stackBits, localData,
      counterStacks, Fin.sum_univ_two]
  rw [hinit] at hg
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
