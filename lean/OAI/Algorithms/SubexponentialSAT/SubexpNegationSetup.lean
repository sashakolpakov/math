import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNegationProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPredecessorProgram

namespace OAI.Algorithms

/-! Actual runtime preparation of the modular-negation constant. -/

namespace SubexponentialSAT.SubexpNegationSetup

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms
open SubexponentialSAT.ModularRingPrograms SubexponentialSAT.SubexpNegationProgram

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

abbrev workState (input modulus operand shape constant : List Bool) : Fin 9 → List Bool :=
  ![input, operand, [], [], [], modulus, [], shape, constant]

private theorem embed_ports {s l : ℕ} (port : Fin s → Fin 9)
    (hinj : Function.Injective port) (pc : Option (Fin l))
    (regs frameRegs : Fin 8 → Bool) (localStk : Fin s → List Bool)
    (frame target : Fin 9 → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 9 l)
      ⟨pc, regs, localStk⟩ = ⟨pc, regs, target⟩ := by
  have hp : (embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 9 l)
      ⟨pc, regs, localStk⟩).pc = pc := by cases pc <;> rfl
  have hr : (embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 9 l)
      ⟨pc, regs, localStk⟩).regs = regs := by simp [embedCfg]
  have hs : (embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 9 l)
      ⟨pc, regs, localStk⟩).stacks = target := by
    funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port id none _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port id none _ _ i hi).trans (hframe i hi).symm
  exact cfg_ext hp hr hs

private theorem sequence_runs {l m n k : ℕ}
    (p : Program 8 9 l) (q : Program 8 9 m)
    (ra rb rc : Fin 8 → Bool) (sa sb sc : Fin 9 → List Bool)
    (hp : RunsIn p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : RunsIn q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    RunsIn (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ :=
  link_runsIn p q hp rfl hq

abbrev copyModulusProgram : Program 8 9 8 := copyProgram 5 1 2 1 3

private theorem copy_modulus (input modulus : List Bool) :
    copyStacks (5 : Fin 9) 1 (state input modulus []) =
      workState input modulus modulus [] [] := by
  funext i; fin_cases i <;> simp [copyStacks, state, extendEight, extendSeven,
    resting, seven, workState]

theorem copyModulus_trace (regs : Fin 8 → Bool) (input modulus : List Bool) :
    Trace copyModulusProgram (7 * modulus.length + 5)
      ⟨some 0, regs, state input modulus []⟩
      ⟨none, readRegs regs 1 3 none, workState input modulus modulus [] []⟩ := by
  have ht := copyProgram_trace (5 : Fin 9) 1 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (state input modulus []) (by rfl)
  have hh := halt_after_trace copyModulusProgram ht (7 : Fin 8) rfl rfl
  simp only [copyResult, copy_modulus] at hh
  simpa [state, extendEight, extendSeven, resting, seven, Nat.add_assoc] using hh

def predecessorPorts : Fin 3 → Fin 9 := ![1, 6, 8]
theorem predecessorPorts_injective : Function.Injective predecessorPorts := by decide

abbrev widePredecessorProgram : Program 8 9 9 :=
  liftProgram SubexponentialSAT.SubexpPredecessorProgram.predecessorProgram id predecessorPorts

private theorem predecessor_port_value (input modulus operand output : List Bool) (i : Fin 3) :
    workState input modulus operand [] output (predecessorPorts i) =
      SubexponentialSAT.ModularPrograms.operandStacks operand [] output i := by
  fin_cases i <;> rfl

private theorem predecessor_stack_updates (input modulus operand output : List Bool) :
    workState input modulus operand [] output =
      Function.update (Function.update (state input modulus []) 1 operand) 8 output := by
  funext i
  fin_cases i <;> simp [workState, state, extendEight, extendSeven, resting, seven]

private theorem predecessor_port_frame (input modulus operand output : List Bool)
    (i : Fin 9) (hi : ¬ ∃ j, predecessorPorts j = i) :
    workState input modulus operand [] output i = state input modulus [] i := by
  have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
  have h8 : i ≠ 8 := fun h => hi ⟨2, h.symm⟩
  rw [predecessor_stack_updates]
  simp only [Function.update_noteq h8, Function.update_noteq h1]

private theorem embed_predecessor (pc : Option (Fin 9))
    (regs frameRegs : Fin 8 → Bool) (input modulus operand output : List Bool) :
    embedCfg id predecessorPorts id none
      (⟨none, frameRegs, state input modulus []⟩ : Cfg 8 9 9)
      (SubexponentialSAT.SubexpPredecessorProgram.cfg pc regs operand output) =
      ⟨pc, regs, workState input modulus operand [] output⟩ := by
  exact embed_ports predecessorPorts predecessorPorts_injective pc regs frameRegs
    (SubexponentialSAT.ModularPrograms.operandStacks operand [] output) (state input modulus [])
    (workState input modulus operand [] output)
    (predecessor_port_value input modulus operand output)
    (predecessor_port_frame input modulus operand output)

def predecessorWord (modulus : List Bool) : List Bool :=
  (subCarry true modulus (List.replicate modulus.length false)).1

theorem widePredecessor_trace (regs : Fin 8 → Bool) (input modulus : List Bool) :
    ∃ finalRegs,
      Trace widePredecessorProgram (7 * modulus.length + 4)
        ⟨some 0, regs, workState input modulus modulus [] []⟩
        ⟨none, finalRegs, workState input modulus [] [] (predecessorWord modulus).reverse⟩ := by
  obtain ⟨rf, ht⟩ := SubexponentialSAT.SubexpPredecessorProgram.predecessor_trace regs modulus
  have hw := liftProgram_trace SubexponentialSAT.SubexpPredecessorProgram.predecessorProgram id predecessorPorts
    (⟨none, regs, state input modulus []⟩ : Cfg 8 9 9)
    Function.injective_id predecessorPorts_injective ht
  rw [embed_predecessor, embed_predecessor] at hw
  exact ⟨rf, hw⟩

abbrev reverseConstantProgram : Program 8 9 10 := reverseProgram 8 1 2 1 3

private theorem reverse_constant (input modulus constant : List Bool) :
    reverseStacks (8 : Fin 9) (workState input modulus [] [] constant.reverse) =
      workState input modulus [] [] constant := by
  funext i; fin_cases i <;> simp [reverseStacks, workState]

theorem reverseConstant_trace (regs : Fin 8 → Bool) (input modulus constant : List Bool) :
    Trace reverseConstantProgram (9 * constant.length + 7)
      ⟨some 0, regs, workState input modulus [] [] constant.reverse⟩
      ⟨none, readRegs regs 1 3 none, workState input modulus [] [] constant⟩ := by
  have ht := reverseProgram_trace (8 : Fin 9) 1 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (workState input modulus [] [] constant.reverse) (by rfl) (by rfl)
  have hh := halt_after_trace reverseConstantProgram ht (9 : Fin 10) rfl rfl
  simp only [reverseResult, reverse_constant] at hh
  simpa [workState, Nat.add_assoc] using hh

abbrev copyShapeProgram : Program 8 9 8 := copyProgram 0 7 2 1 3

private theorem copy_shape (input modulus constant : List Bool) :
    copyStacks (0 : Fin 9) 7 (workState input modulus [] [] constant) =
      workState input modulus [] input constant := by
  funext i; fin_cases i <;> simp [copyStacks, workState]

theorem copyShape_trace (regs : Fin 8 → Bool) (input modulus constant : List Bool) :
    Trace copyShapeProgram (7 * input.length + 5)
      ⟨some 0, regs, workState input modulus [] [] constant⟩
      ⟨none, readRegs regs 1 3 none, workState input modulus [] input constant⟩ := by
  have ht := copyProgram_trace (0 : Fin 9) 7 2 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (workState input modulus [] [] constant) (by rfl)
  have hh := halt_after_trace copyShapeProgram ht (7 : Fin 8) rfl rfl
  simp only [copyResult, copy_shape] at hh
  simpa [workState, Nat.add_assoc] using hh

def normalizePorts : Fin 8 → Fin 9 := ![8, 1, 2, 3, 4, 5, 6, 7]
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

abbrev normalizeConstantProgram : Program 8 9 12 :=
  liftProgram normalizeProgram id normalizePorts

private theorem normalization_port_value (input modulus constant shape : List Bool) (i : Fin 8) :
    workState input modulus [] shape constant (normalizePorts i) =
      normalizationState constant shape [] modulus i := by
  fin_cases i <;> rfl

private theorem normalization_stack_updates (input modulus constant shape : List Bool) :
    workState input modulus [] shape constant =
      Function.update (Function.update (state input modulus []) 7 shape) 8 constant := by
  funext i
  fin_cases i <;> simp [workState, state, extendEight, extendSeven, resting, seven]

private theorem normalization_port_frame (input modulus constant shape : List Bool)
    (i : Fin 9) (hi : ¬ ∃ j, normalizePorts j = i) :
    workState input modulus [] shape constant i = state input modulus [] i := by
  have h7 : i ≠ 7 := fun h => hi ⟨7, h.symm⟩
  have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
  rw [normalization_stack_updates]
  simp only [Function.update_noteq h8, Function.update_noteq h7]

private theorem embed_normalization (pc : Option (Fin 12))
    (regs frameRegs : Fin 8 → Bool) (input modulus constant shape : List Bool) :
    embedCfg id normalizePorts id none
      (⟨none, frameRegs, state input modulus []⟩ : Cfg 8 9 12)
      ⟨pc, regs, normalizationState constant shape [] modulus⟩ =
      ⟨pc, regs, workState input modulus [] shape constant⟩ := by
  exact embed_ports normalizePorts normalizePorts_injective pc regs frameRegs
    (normalizationState constant shape [] modulus) (state input modulus [])
    (workState input modulus [] shape constant)
    (normalization_port_value input modulus constant shape)
    (normalization_port_frame input modulus constant shape)

theorem normalizeConstant_correct (regs : Fin 8 → Bool)
    (input modulus constant : List Bool) :
    ∃ finalRegs,
      RunsIn normalizeConstantProgram (7 * input.length + 2 * constant.length + 9)
        ⟨some 0, regs, workState input modulus [] input constant⟩
        ⟨none, finalRegs, state input modulus (padTo input constant)⟩ := by
  obtain ⟨rf, ht⟩ := normalize_correct regs constant input modulus
  have hw := liftProgram_runsIn normalizeProgram id normalizePorts
    (⟨none, regs, state input modulus []⟩ : Cfg 8 9 12)
    Function.injective_id normalizePorts_injective ht
  rw [embed_normalization, embed_normalization] at hw
  exact ⟨rf, hw⟩

/-- Builds the reusable constant, preserving both the input and its modulus. -/
abbrev setupProgram : Program 8 9 47 :=
  { link (link (link (link copyModulusProgram widePredecessorProgram)
      reverseConstantProgram) copyShapeProgram) normalizeConstantProgram with
    inputStack := 0, outputStack := 8 }

def preparedConstant (input modulus : List Bool) : List Bool :=
  padTo input (predecessorWord modulus)

theorem setup_execute (regs : Fin 8 → Bool) (input modulus : List Bool) :
    ∃ finalRegs,
      RunsIn setupProgram (25 * modulus.length + 14 * input.length + 30)
        ⟨some 0, regs, state input modulus []⟩
        ⟨none, finalRegs, state input modulus (preparedConstant input modulus)⟩ := by
  have h1 := copyModulus_trace regs input modulus
  obtain ⟨r2, h2⟩ := widePredecessor_trace (readRegs regs 1 3 none) input modulus
  have h3 := reverseConstant_trace r2 input modulus (predecessorWord modulus)
  have h4 := copyShape_trace (readRegs r2 1 3 none) input modulus (predecessorWord modulus)
  obtain ⟨r5, h5⟩ := normalizeConstant_correct (readRegs (readRegs r2 1 3 none) 1 3 none)
    input modulus (predecessorWord modulus)
  have h12 := sequence_runs copyModulusProgram widePredecessorProgram _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ ⟨_, le_rfl, h2⟩
  have h123 := sequence_runs _ reverseConstantProgram _ _ _ _ _ _
    h12 ⟨_, le_rfl, h3⟩
  have h1234 := sequence_runs _ copyShapeProgram _ _ _ _ _ _
    h123 ⟨_, le_rfl, h4⟩
  have ht := sequence_runs _ normalizeConstantProgram _ _ _ _ _ _ h1234 h5
  refine ⟨r5, ht.mono ?_⟩
  simp only [predecessorWord, SubexponentialSAT.SubexpPredecessorProgram.predecessor_length]
  omega

theorem preparedConstant_length (input modulus : List Bool) :
    (preparedConstant input modulus).length = input.length := padTo_length _ _

theorem preparedConstant_value (input modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ input.length) :
    BinaryArithmetic.toNat (preparedConstant input modulus) = BinaryArithmetic.toNat modulus - 1 := by
  have hp := SubexponentialSAT.SubexpPredecessorProgram.predecessor_value modulus hm
  change BinaryArithmetic.toNat (padTo input (predecessorWord modulus)) = _
  rw [padTo_value_of_lt]
  · exact hp
  · change BinaryArithmetic.toNat (subCarry true modulus (List.replicate modulus.length false)).1 < _
    rw [hp]
    omega

theorem preparedConstant_cast (input modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ input.length) :
    (BinaryArithmetic.toNat (preparedConstant input modulus) : ZMod (BinaryArithmetic.toNat modulus)) = -1 := by
  rw [preparedConstant_value input modulus hm hcapacity,
    Nat.cast_sub (by omega : 1 ≤ BinaryArithmetic.toNat modulus), ZMod.natCast_self,
    Nat.cast_one, zero_sub]

theorem setup_value (regs : Fin 8 → Bool) (input modulus : List Bool) (B : ℕ)
    (hx : input.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs constant,
      RunsIn setupProgram (60 * (B + 1))
        ⟨some 0, regs, state input modulus []⟩
        ⟨none, finalRegs, state input modulus constant⟩ ∧
      constant.length = B ∧ BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1 := by
  obtain ⟨rf, ht⟩ := setup_execute regs input modulus
  refine ⟨rf, preparedConstant input modulus, ht.mono ?_, ?_, ?_⟩
  · omega
  · rw [preparedConstant_length, hx]
  · apply preparedConstant_value input modulus hm
    simpa [hx] using hcapacity

/-- One complete call also prepares its own negation constant from the modulus. -/
abbrev preparedNegationProgram : Program 8 9 196 := link setupProgram negationProgram

theorem preparedNegation_value (regs : Fin 8 → Bool) (input modulus : List Bool) (B : ℕ)
    (hx : input.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output constant,
      RunsIn preparedNegationProgram (6070 * (B + 1) ^ 2)
        ⟨some 0, regs, state input modulus []⟩
        ⟨none, finalRegs, state output modulus constant⟩ ∧
      output.length = B ∧ constant.length = B ∧
      BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1 ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat modulus - BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus) % BinaryArithmetic.toNat modulus := by
  obtain ⟨r1, c, h1, hclen, hcv⟩ := setup_value regs input modulus B hx hmLength hm hcapacity
  obtain ⟨rf, output, h2, hlen, hv⟩ :=
    negation_value r1 input modulus c B hx hclen hmLength hm hcapacity hcv
  have ht := sequence_runs setupProgram negationProgram _ _ _ _ _ _ h1 h2
  refine ⟨rf, output, c, ht.mono ?_, hlen, hclen, hcv, hv⟩
  nlinarith only []

theorem preparedNegation_primitive (regs : Fin 8 → Bool) (input modulus : List Bool) (B : ℕ)
    (hx : input.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output constant,
      SubexponentialSAT.Computation.RunsIn (primitive preparedNegationProgram).step
        (primitiveOverhead preparedNegationProgram * (6070 * (B + 1) ^ 2))
        (primitiveCfg preparedNegationProgram ⟨some 0, regs, state input modulus []⟩)
        (primitiveCfg preparedNegationProgram ⟨none, finalRegs, state output modulus constant⟩) ∧
      output.length = B ∧ constant.length = B ∧
      BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1 ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) = -(BinaryArithmetic.toNat input : ZMod (BinaryArithmetic.toNat modulus)) := by
  obtain ⟨rf, output, c, ht, hlen, hclen, hcv, hv⟩ :=
    preparedNegation_value regs input modulus B hx hmLength hm hcapacity
  refine ⟨rf, output, c, primitive_execution _ ht, hlen, hclen, hcv, ?_⟩
  rw [hv, ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hm).le,
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]

/-- A noncanonical input exercises reduction before interpreting negation. -/
theorem unreduced_fourteen_mod_thirteen (regs : Fin 8 → Bool) :
    ∃ finalRegs output constant,
      RunsIn preparedNegationProgram (6070 * (4 + 1)^2)
        ⟨some 0, regs, state [false, true, true, true] [true, false, true, true] []⟩
        ⟨none, finalRegs, state output [true, false, true, true] constant⟩ ∧
      output.length = 4 ∧ BinaryArithmetic.toNat output = 12 := by
  obtain ⟨rf, output, constant, ht, hlen, _, _, hv⟩ := preparedNegation_value regs
    [false, true, true, true] [true, false, true, true] 4
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨rf, output, constant, ht, hlen, hv⟩

/-- Zero at the full-capacity modulus exercises the B+1-bit setup path. -/
theorem zero_mod_sixteen (regs : Fin 8 → Bool) :
    ∃ finalRegs output constant,
      RunsIn preparedNegationProgram (6070 * (4 + 1)^2)
        ⟨some 0, regs, state [false, false, false, false]
          [false, false, false, false, true] []⟩
        ⟨none, finalRegs, state output [false, false, false, false, true] constant⟩ ∧
      output.length = 4 ∧ BinaryArithmetic.toNat output = 0 ∧ BinaryArithmetic.toNat constant = 15 := by
  obtain ⟨rf, output, constant, ht, hlen, _, hc, hv⟩ := preparedNegation_value regs
    [false, false, false, false] [false, false, false, false, true] 4
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨rf, output, constant, ht, hlen, hv, hc⟩

end SubexponentialSAT.SubexpNegationSetup

end OAI.Algorithms
