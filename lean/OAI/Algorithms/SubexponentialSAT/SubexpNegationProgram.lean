import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms

namespace OAI.Algorithms

/-!
# A finite modular-negation program

The runtime words are little-endian Boolean stacks. Stack 0 holds the operand,
stack 5 the positive modulus, and stack 8 a prepared word of value modulus - 1.
All other stacks start empty. A preserving copy supplies the second operand of
the verified multiplication program; both the modulus and the prepared word
survive the call. No reducedness assumption is made about the operand.
-/

namespace SubexponentialSAT.SubexpNegationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms
open SubexponentialSAT.ModularRingPrograms

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

def extendEight (base : Fin 8 → List Bool) (constant : List Bool) : Fin 9 → List Bool :=
  ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, base 7, constant]

def state (input modulus constant : List Bool) : Fin 9 → List Bool :=
  extendEight (extendSeven (resting input modulus []) []) constant

def ready (input modulus constant : List Bool) : Fin 9 → List Bool :=
  extendEight (extendSeven (scalarInput input constant modulus) []) constant

abbrev coefficientCopyProgram : Program 8 9 8 := copyProgram 8 1 2 1 3

private theorem copy_coefficient (input modulus constant : List Bool) :
    copyStacks (8 : Fin 9) 1 (state input modulus constant) =
      ready input modulus constant := by
  funext i
  fin_cases i <;> simp [copyStacks, state, ready, extendEight, extendSeven,
    resting, scalarInput, seven]

theorem coefficientCopy_trace (regs : Fin 8 → Bool) (input modulus constant : List Bool) :
    Trace coefficientCopyProgram (7 * constant.length + 5)
      ⟨some 0, regs, state input modulus constant⟩
      ⟨none, readRegs regs 1 3 none, ready input modulus constant⟩ := by
  have ht := copyProgram_trace (8 : Fin 9) 1 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (state input modulus constant) (by rfl)
  have hh := halt_after_trace coefficientCopyProgram ht (7 : Fin 8) rfl rfl
  simp only [copyResult, copy_coefficient] at hh
  simpa [state, extendEight, Nat.add_assoc] using hh

def eightPorts : Fin 8 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7]

theorem eightPorts_injective : Function.Injective eightPorts := by decide

private theorem embed_eight {l : ℕ} (pc : Option (Fin l))
    (regs frameRegs : Fin 8 → Bool) (base frameBase : Fin 8 → List Bool)
    (constant : List Bool) :
    embedCfg id eightPorts id none
      (⟨none, frameRegs, extendEight frameBase constant⟩ : Cfg 8 9 l)
      ⟨pc, regs, base⟩ = ⟨pc, regs, extendEight base constant⟩ := by
  have hp : (embedCfg id eightPorts id none
      (⟨none, frameRegs, extendEight frameBase constant⟩ : Cfg 8 9 l)
      ⟨pc, regs, base⟩).pc = pc := by cases pc <;> rfl
  have hr : (embedCfg id eightPorts id none
      (⟨none, frameRegs, extendEight frameBase constant⟩ : Cfg 8 9 l)
      ⟨pc, regs, base⟩).regs = regs := by simp [embedCfg]
  have hs : (embedCfg id eightPorts id none
      (⟨none, frameRegs, extendEight frameBase constant⟩ : Cfg 8 9 l)
      ⟨pc, regs, base⟩).stacks = extendEight base constant := by
    funext i
    have hi (j : Fin 8) := embedCfg_stack id eightPorts id none
      (⟨none, frameRegs, extendEight frameBase constant⟩ : Cfg 8 9 l)
      ⟨pc, regs, base⟩ eightPorts_injective j
    fin_cases i
    · exact hi 0
    · exact hi 1
    · exact hi 2
    · exact hi 3
    · exact hi 4
    · exact hi 5
    · exact hi 6
    · exact hi 7
    · exact embedCfg_stack_frame id eightPorts id none _ _ 8 (by decide)
  exact cfg_ext hp hr hs

abbrev wideMultiplyProgram : Program 8 9 141 := liftProgram wordMulProgram id eightPorts

/-- A fixed table: eight copy labels followed by 141 verified multiplication labels. -/
abbrev negationProgram : Program 8 9 149 :=
  { link coefficientCopyProgram wideMultiplyProgram with inputStack := 0 }

theorem negationProgram_input : negationProgram.inputStack = 0 := rfl
theorem negationProgram_output : negationProgram.outputStack = 0 := rfl

/-- The complete finite execution preserves both supplied constant words. -/
theorem negation_execute (regs : Fin 8 → Bool) (input modulus constant : List Bool) (B : ℕ)
    (hx : input.length = B) (hc : constant.length = B)
    (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      RunsIn negationProgram (6010 * (B + 1) ^ 2)
        ⟨some 0, regs, state input modulus constant⟩
        ⟨none, finalRegs, state output modulus constant⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat input * BinaryArithmetic.toNat constant) % BinaryArithmetic.toNat modulus := by
  have hcopy := coefficientCopy_trace regs input modulus constant
  obtain ⟨rf, output, hr, hlen, hv⟩ := wordMul_value (readRegs regs 1 3 none)
    input constant modulus B hx hc hmLength hm hcapacity
  have hwide := liftProgram_runsIn wordMulProgram id eightPorts
    (⟨none, regs, state [] modulus constant⟩ : Cfg 8 9 141)
    Function.injective_id eightPorts_injective hr
  dsimp only [state] at hwide
  rw [embed_eight, embed_eight] at hwide
  have ht := link_runsIn coefficientCopyProgram wideMultiplyProgram
    (show RunsIn coefficientCopyProgram (7 * constant.length + 5) _ _ from
      ⟨_, le_rfl, hcopy⟩) rfl hwide
  refine ⟨rf, output, ?_, hlen, hv⟩
  have hbound : 7 * constant.length + 5 + 6000 * (B + 1) ^ 2 ≤
      6010 * (B + 1) ^ 2 := by rw [hc]; nlinarith only []
  exact ht.mono hbound

theorem mul_predecessor_mod (x m : ℕ) (hm : 0 < m) :
    (x * (m - 1)) % m = (m - x % m) % m := by
  apply (ZMod.natCast_eq_natCast_iff' _ _ m).mp
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), ZMod.natCast_self,
    Nat.cast_one, zero_sub, mul_neg, mul_one,
    Nat.cast_sub (Nat.mod_lt x hm).le, ZMod.natCast_self,
    ZMod.natCast_mod, zero_sub]

/-- Numeric modular negation, including inputs at least as large as the modulus. -/
theorem negation_value (regs : Fin 8 → Bool) (input modulus constant : List Bool) (B : ℕ)
    (hx : input.length = B) (hc : constant.length = B)
    (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (hconstant : BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1) :
    ∃ finalRegs output,
      RunsIn negationProgram (6010 * (B + 1) ^ 2)
        ⟨some 0, regs, state input modulus constant⟩
        ⟨none, finalRegs, state output modulus constant⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat modulus - BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus) % BinaryArithmetic.toNat modulus := by
  obtain ⟨rf, output, ht, hlen, hv⟩ :=
    negation_execute regs input modulus constant B hx hc hmLength hm hcapacity
  refine ⟨rf, output, ht, hlen, ?_⟩
  rw [hv, hconstant, mul_predecessor_mod _ _ hm]

theorem negation_cast (regs : Fin 8 → Bool) (input modulus constant : List Bool) (B : ℕ)
    (hx : input.length = B) (hc : constant.length = B)
    (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (hconstant : BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1) :
    ∃ finalRegs output,
      RunsIn negationProgram (6010 * (B + 1) ^ 2)
        ⟨some 0, regs, state input modulus constant⟩
        ⟨none, finalRegs, state output modulus constant⟩ ∧
      output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) = -(BinaryArithmetic.toNat input : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨rf, output, ht, hlen, hv⟩ :=
    negation_value regs input modulus constant B hx hc hmLength hm hcapacity hconstant
  refine ⟨rf, output, ht, hlen, ?_⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hm).le,
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

theorem negation_primitive (regs : Fin 8 → Bool) (input modulus constant : List Bool) (B : ℕ)
    (hx : input.length = B) (hc : constant.length = B)
    (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B)
    (hconstant : BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1) :
    ∃ finalRegs output,
      SubexponentialSAT.Computation.RunsIn (primitive negationProgram).step
        (primitiveOverhead negationProgram * (6010 * (B + 1) ^ 2))
        (primitiveCfg negationProgram ⟨some 0, regs, state input modulus constant⟩)
        (primitiveCfg negationProgram ⟨none, finalRegs, state output modulus constant⟩) ∧
      output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) = -(BinaryArithmetic.toNat input : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨rf, output, ht, hlen, hv⟩ :=
    negation_cast regs input modulus constant B hx hc hmLength hm hcapacity hconstant
  exact ⟨rf, output, primitive_execution _ ht, hlen, hv⟩

end SubexponentialSAT.SubexpNegationProgram

end OAI.Algorithms
