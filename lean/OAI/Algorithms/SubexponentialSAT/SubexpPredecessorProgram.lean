import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms

namespace OAI.Algorithms

/-! A nine-label bit program for fixed-width binary decrement. -/

namespace SubexponentialSAT.SubexpPredecessorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularArithmetic SubexponentialSAT.BinaryArithmetic

/-- Register 0 is the borrow. The initializer sets it to one, after which
each bit uses XOR and AND to propagate that borrow through the runtime word. -/
abbrev predecessorProgram : Program 8 3 9 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code := ![.set 0 true 1, .pop 0 1 3 2, .branch 3 3 8,
    .bxor 2 1 0 4, .bnot 1 1 5, .band 0 1 0 6, .push 2 2 7,
    .goto 1, .halt]

def cfg (pc : Option (Fin 9)) (regs : Fin 8 → Bool) (input output : List Bool) :
    Cfg 8 3 9 := ⟨pc, regs, operandStacks input [] output⟩

def roundRegs (regs : Fin 8 → Bool) (b : Bool) : Fin 8 → Bool :=
  let r := readRegs regs 1 3 (some b)
  let r := Function.update r 2 (b ^^ regs 0)
  let r := Function.update r 1 (!b)
  Function.update r 0 ((!b) && regs 0)

private theorem update_left (input output next : List Bool) :
    Function.update (operandStacks input [] output) 0 next =
      operandStacks next [] output := by
  funext i; fin_cases i <;> simp [operandStacks]

private theorem update_output (input output next : List Bool) :
    Function.update (operandStacks input [] output) 2 next =
      operandStacks input [] next := by
  funext i; fin_cases i <;> simp [operandStacks]

theorem round_trace (regs : Fin 8 → Bool) (b : Bool) (input output : List Bool) :
    Trace predecessorProgram 7
      (cfg (some 1) regs (b :: input) output)
      (cfg (some 1) (roundRegs regs b) input ((b ^^ regs 0) :: output)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, predecessorProgram, execInstr,
    cfg, readRegs, roundRegs, update_left, update_output, Function.update_apply]

theorem exit_trace (regs : Fin 8 → Bool) (output : List Bool) :
    Trace predecessorProgram 3
      (cfg (some 1) regs [] output)
      (cfg none (readRegs regs 1 3 none) [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, predecessorProgram, execInstr,
    cfg, readRegs, update_left, Function.update_apply]

theorem loop_trace (regs : Fin 8 → Bool) (input output : List Bool) :
    ∃ finalRegs,
      Trace predecessorProgram (7 * input.length + 3)
        (cfg (some 1) regs input output)
        (cfg none finalRegs []
          ((subCarry (regs 0) input (List.replicate input.length false)).1.reverse ++ output)) := by
  induction input generalizing regs output with
  | nil =>
    exact ⟨readRegs regs 1 3 none, by simpa [subCarry] using exit_trace regs output⟩
  | cons b input ih =>
    obtain ⟨rf, ht⟩ := ih (roundRegs regs b) ((b ^^ regs 0) :: output)
    refine ⟨rf, ?_⟩
    have hall := (round_trace regs b input output).trans ht
    convert hall using 1 <;>
      simp [subCarry, List.replicate_succ, List.reverse_cons, List.append_assoc,
        roundRegs, borrowBit, differenceBit] ; omega

/-- Exact execution count, with a direct connection to the verified subtractor. -/
theorem predecessor_trace (regs : Fin 8 → Bool) (input : List Bool) :
    ∃ finalRegs,
      Trace predecessorProgram (7 * input.length + 4)
        (cfg (some 0) regs input [])
        (cfg none finalRegs []
          (subCarry true input (List.replicate input.length false)).1.reverse) := by
  have hs : Trace predecessorProgram 1
      (cfg (some 0) regs input [])
      (cfg (some 1) (Function.update regs 0 true) input []) := by
    apply SubexponentialSAT.Computation.Trace.of_iterate
    simp [ step, predecessorProgram, execInstr, cfg]
  obtain ⟨rf, ht⟩ := loop_trace (Function.update regs 0 true) input []
  refine ⟨rf, ?_⟩
  have hall := hs.trans ht
  convert hall using 1 <;> simp_all ; omega

@[simp] theorem toNat_replicate_false (n : ℕ) :
    BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toNat_cons, bitVal, ih]

theorem predecessor_value (input : List Bool) (hpositive : 0 < BinaryArithmetic.toNat input) :
    BinaryArithmetic.toNat (subCarry true input (List.replicate input.length false)).1 = BinaryArithmetic.toNat input - 1 := by
  have hlen : input.length = (List.replicate input.length false).length := by simp
  have hv := subCarry_correct true input (List.replicate input.length false) hlen
  have hb := toNat_lt_pow_length (subCarry true input (List.replicate input.length false)).1
  rw [subCarry_length true _ _ hlen] at hb
  cases hborrow : (subCarry true input (List.replicate input.length false)).2 <;>
    simp [hborrow, bitVal] at hv <;> omega

theorem predecessor_length (input : List Bool) :
    (subCarry true input (List.replicate input.length false)).1.length = input.length :=
  subCarry_length _ _ _ (by simp)

theorem predecessor_thirteen :
    (subCarry true [true, false, true, true]
      [false, false, false, false]).1 = [false, false, true, true] := by decide

theorem predecessor_power_of_two :
    (subCarry true [false, false, false, false, true]
      [false, false, false, false, false]).1 = [true, true, true, true, false] := by decide

end SubexponentialSAT.SubexpPredecessorProgram

end OAI.Algorithms
