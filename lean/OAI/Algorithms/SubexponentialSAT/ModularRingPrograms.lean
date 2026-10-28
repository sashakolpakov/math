import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularRingCore

namespace OAI.Algorithms

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

/-! ## Restore a runtime-specified output width -/

open SubexponentialSAT.ModularPrograms

private theorem update_operand_left (left right output next : List Bool) :
    Function.update (operandStacks left right output) 0 next =
      operandStacks next right output := by
  funext i; fin_cases i <;> simp [operandStacks]

theorem paddingPrefix_exit (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3
      (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, update_operand_left, Function.update_apply]

/-- The padding loop also handles a longer input: its unconsumed suffix remains
on the input stack, so a subsequent measured clear loop can remove it. -/
theorem paddingPrefix_correct (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ finalRegs,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none finalRegs [] (input.drop shape.length)
          ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
    exact ⟨readRegs regs 1 3 none, by simpa [padTo] using paddingPrefix_exit regs input output⟩
  | cons a shape ih =>
    cases input with
    | nil =>
      obtain ⟨rf, hr⟩ := ih (paddingRegs regs a []) [] (false :: output)
      refine ⟨rf, ?_⟩
      have ht := (padding_round regs a shape [] output).trans hr
      convert ht using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] ; omega
    | cons b bs =>
      obtain ⟨rf, hr⟩ := ih (paddingRegs regs a (b :: bs)) bs (b :: output)
      refine ⟨rf, ?_⟩
      have ht := (padding_round regs a shape (b :: bs) output).trans hr
      convert ht using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] ; omega

theorem padTo_value_of_lt (shape input : List Bool)
    (hvalue : BinaryArithmetic.toNat input < 2 ^ shape.length) :
    BinaryArithmetic.toNat (padTo shape input) = BinaryArithmetic.toNat input := by
  induction shape generalizing input with
  | nil =>
    simp only [List.length_nil, pow_zero] at hvalue
    have hz : BinaryArithmetic.toNat input = 0 := by omega
    simp [padTo, hz]
  | cons a shape ih =>
    cases input with
    | nil => exact padTo_correct _ [] (by simp)
    | cons b bs =>
      have htail : BinaryArithmetic.toNat bs < 2 ^ shape.length := by
        simp only [toNat_cons, List.length_cons, pow_succ] at hvalue
        omega
      simpa [padTo, toNat_cons] using congrArg (fun n => bitVal b + 2 * n) (ih bs htail)

def extendSeven (base : Fin 7 → List Bool) (shape : List Bool) : Fin 8 → List Bool :=
  ![base 0, base 1, base 2, base 3, base 4, base 5, base 6, shape]

def sevenPorts : Fin 7 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6]
def normalizePorts : Fin 3 → Fin 8 := ![7, 0, 2]

theorem sevenPorts_injective : Function.Injective sevenPorts := by decide
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

private theorem embed_seven {l : ℕ} (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (base frameBase : Fin 7 → List Bool) (shape : List Bool) :
    embedCfg id sevenPorts id none
      (⟨none, frameRegs, extendSeven frameBase shape⟩ : Cfg 8 8 l)
      ⟨pc, regs, base⟩ = ⟨pc, regs, extendSeven base shape⟩ := by
  apply embed_ports sevenPorts sevenPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

abbrev normalizationState (input shape output modulus : List Bool) : Fin 8 → List Bool :=
  ![input, [], output, [], [], modulus, [], shape]

private theorem normalization_port_value (input shape output modulus : List Bool)
    (i : Fin 3) :
    normalizationState input shape output modulus (normalizePorts i) =
      operandStacks shape input output i := by
  fin_cases i <;> rfl

private theorem normalizationState_apply (input shape output modulus : List Bool) :
    normalizationState input shape output modulus = fun i =>
      if i = 0 then input else if i = 2 then output else
      if i = 5 then modulus else if i = 7 then shape else [] := by
  funext i
  fin_cases i <;> rfl

private theorem normalization_port_frame (input shape output modulus : List Bool)
    (i : Fin 8) (hi : ¬ ∃ j, normalizePorts j = i) :
    normalizationState input shape output modulus i =
      normalizationState [] [] [] modulus i := by
  have h0 : i ≠ 0 := by
    intro h; subst i; exact hi ⟨1, rfl⟩
  have h2 : i ≠ 2 := by
    intro h; subst i; exact hi ⟨2, rfl⟩
  have h7 : i ≠ 7 := by
    intro h; subst i; exact hi ⟨0, rfl⟩
  simp only [normalizationState_apply, h0, h2, h7, ite_false]

private theorem embed_normalize (pc : Option (Fin 5)) (regs frameRegs : Fin 8 → Bool)
    (input shape output modulus : List Bool) :
    embedCfg id normalizePorts id none
      (⟨none, frameRegs, normalizationState [] [] [] modulus⟩ : Cfg 8 8 5)
      (paddingCfg pc regs shape input output) =
      ⟨pc, regs, normalizationState input shape output modulus⟩ := by
  exact embed_ports normalizePorts normalizePorts_injective pc regs frameRegs
    (operandStacks shape input output) (normalizationState [] [] [] modulus)
    (normalizationState input shape output modulus)
    (normalization_port_value input shape output modulus)
    (normalization_port_frame input shape output modulus)

abbrev normalizationPrefixProgram : Program 8 8 5 :=
  liftProgram paddingProgram id normalizePorts

theorem normalizationPrefix_correct (regs : Fin 8 → Bool) (input shape modulus : List Bool) :
    ∃ finalRegs,
      Trace normalizationPrefixProgram (4 * shape.length + 3)
        ⟨some 0, regs, normalizationState input shape [] modulus⟩
        ⟨none, finalRegs,
          normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus⟩ := by
  obtain ⟨rf, hr⟩ := paddingPrefix_correct regs shape input []
  have hw := liftProgram_trace paddingProgram id normalizePorts
    (⟨none, regs, normalizationState [] [] [] modulus⟩ : Cfg 8 8 5)
    Function.injective_id normalizePorts_injective hr
  rw [embed_normalize, embed_normalize] at hw
  exact ⟨rf, by simpa using hw⟩

abbrev normalizationClearProgram : Program 8 8 3 := clearProgram 0 1 3
abbrev normalizationMoveProgram : Program 8 8 4 := transferProgram 2 0 1 3
abbrev normalizeProgram : Program 8 8 12 :=
  link (link normalizationPrefixProgram normalizationClearProgram) normalizationMoveProgram

private theorem normalization_clear (input output modulus : List Bool) :
    clearStacks (0 : Fin 8) (normalizationState input [] output modulus) =
      normalizationState [] [] output modulus := by
  funext i; fin_cases i <;> simp [clearStacks, normalizationState]

private theorem normalization_move (output modulus : List Bool) :
    transferStacks (2 : Fin 8) 0 (normalizationState [] [] output.reverse modulus) =
      normalizationState output [] [] modulus := by
  funext i; fin_cases i <;> simp [transferStacks, normalizationState]

theorem normalize_correct (regs : Fin 8 → Bool) (input shape modulus : List Bool) :
    ∃ finalRegs,
      RunsIn normalizeProgram (7 * shape.length + 2 * input.length + 9)
        ⟨some 0, regs, normalizationState input shape [] modulus⟩
        ⟨none, finalRegs, normalizationState (padTo shape input) [] [] modulus⟩ := by
  obtain ⟨r1, h1⟩ := normalizationPrefix_correct regs input shape modulus
  let r2 := readRegs r1 1 3 none
  have tc := clearProgram_trace (0 : Fin 8) (1 : Fin 8) 3 r1
    (normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus)
  have hc := halt_after_trace normalizationClearProgram tc (2 : Fin 3) rfl rfl
  simp only [clearResult, normalization_clear] at hc
  have h2 : Trace normalizationClearProgram (2 * (input.drop shape.length).length + 3)
      ⟨some 0, r1, normalizationState (input.drop shape.length) [] (padTo shape input).reverse modulus⟩
      ⟨none, r2, normalizationState [] [] (padTo shape input).reverse modulus⟩ := by
    simpa [r2, normalizationState, Nat.add_assoc] using hc
  have tm := transferProgram_trace (2 : Fin 8) 0 (1 : Fin 8) 3
    (by decide) (by decide) r2
    (normalizationState [] [] (padTo shape input).reverse modulus)
  have hm := halt_after_trace normalizationMoveProgram tm (3 : Fin 4) rfl rfl
  simp only [transferResult, normalization_move] at hm
  have h3 : Trace normalizationMoveProgram (3 * shape.length + 3)
      ⟨some 0, r2, normalizationState [] [] (padTo shape input).reverse modulus⟩
      ⟨none, r2, normalizationState (padTo shape input) [] [] modulus⟩ := by
    simpa [r2, readRegs_reset, normalizationState, padTo_length, Nat.add_assoc] using hm
  have h12 := sequence_runs normalizationPrefixProgram normalizationClearProgram _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ ⟨_, le_rfl, h2⟩
  have ht := sequence_runs _ normalizationMoveProgram _ _ _ _ _ _ h12 ⟨_, le_rfl, h3⟩
  refine ⟨r2, ht.mono ?_⟩
  simp only [List.length_drop]
  omega

abbrev shapeCopyProgram : Program 8 8 8 := copyProgram 0 7 3 1 3

private theorem shape_copy (xs ys modulus : List Bool) :
    copyStacks (0 : Fin 8) 7 (extendSeven (scalarInput xs ys modulus) []) =
      extendSeven (scalarInput xs ys modulus) xs := by
  funext i; fin_cases i <;> simp [copyStacks, extendSeven, scalarInput, seven]

theorem shapeCopy_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    Trace shapeCopyProgram (7 * xs.length + 5)
      ⟨some 0, regs, extendSeven (scalarInput xs ys modulus) []⟩
      ⟨none, readRegs regs 1 3 none, extendSeven (scalarInput xs ys modulus) xs⟩ := by
  have tc := copyProgram_trace (0 : Fin 8) 7 3 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide)
    regs (extendSeven (scalarInput xs ys modulus) []) (by rfl)
  have hh := halt_after_trace shapeCopyProgram tc (7 : Fin 8) rfl rfl
  simp only [copyResult, shape_copy] at hh
  simpa [extendSeven, scalarInput, seven, Nat.add_assoc] using hh

abbrev canonicalProgram {l : ℕ} (p : Program 8 7 l) : Program 8 8 (8 + l + 12) :=
  link (link shapeCopyProgram (liftProgram p id sevenPorts)) normalizeProgram

/-- Generic measured composition used below with the concrete addition and
multiplication programs. The input's shape is copied by the program itself. -/
theorem canonical_execute {l : ℕ} (p : Program 8 7 l)
    (regs finalRegs : Fin 8 → Bool) (xs ys modulus output : List Bool) (bound : ℕ)
    (hr : RunsIn p bound
      ⟨some p.entry, readRegs regs 1 3 none, scalarInput xs ys modulus⟩
      ⟨none, finalRegs, resting output modulus []⟩) :
    ∃ rf,
      RunsIn (canonicalProgram p)
        (bound + 14 * xs.length + 2 * output.length + 14)
        ⟨some (canonicalProgram p).entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, rf, extendSeven (resting (padTo xs output) modulus []) []⟩ := by
  have h1 := shapeCopy_correct regs xs ys modulus
  have hw := liftProgram_runsIn p id sevenPorts
    (⟨none, regs, extendSeven (resting [] modulus []) xs⟩ : Cfg 8 8 l)
    Function.injective_id sevenPorts_injective hr
  rw [embed_seven, embed_seven] at hw
  obtain ⟨r3, h3⟩ := normalize_correct finalRegs output xs modulus
  have h12 := sequence_runs shapeCopyProgram (liftProgram p id sevenPorts) _ _ _ _ _ _
    ⟨_, le_rfl, h1⟩ hw
  have ht := sequence_runs _ normalizeProgram _ _ _ _ _ _ h12 h3
  refine ⟨r3, ?_⟩
  convert ht using 1
  · omega
  · rfl

abbrev wordAddProgram : Program 8 8 136 := canonicalProgram addModProgram
abbrev wordMulProgram : Program 8 8 141 := canonicalProgram mulModProgram

private theorem word_cost_bound (m x y o B : ℕ)
    (hx : x = B) (hy : y = B) (hm : m ≤ B + 1) (ho : o ≤ m + x + y + 1) :
    600 * (m + x + y + 1) ^ 2 + 14 * x + 2 * o + 14 ≤
      6000 * (B + 1) ^ 2 := by
  have hs : m + x + y + 1 ≤ 3 * (B + 1) := by omega
  have hq : 600 * (m + x + y + 1) ^ 2 ≤ 5400 * (B + 1) ^ 2 := by
    calc
      _ ≤ 600 * (3 * (B + 1)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 2)
      _ = _ := by ring
  have hl : 14 * x + 2 * o + 14 ≤ 20 * (B + 1) := by omega
  have hsq : B + 1 ≤ (B + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left (B + 1) (Nat.le_add_left 1 B)
    simpa only [Nat.mul_one, pow_two] using h
  omega

theorem wordAdd_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      RunsIn wordAddProgram (6000 * (B + 1) ^ 2)
        ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨r1, out, hr, hlen, hv⟩ :=
    addMod_value (readRegs regs 1 3 none) xs ys modulus hm
  obtain ⟨rf, ht⟩ := canonical_execute addModProgram regs r1 xs ys modulus out
    (600 * (modulus.length + xs.length + ys.length + 1) ^ 2) hr
  refine ⟨rf, padTo xs out, ht.mono ?_, ?_, ?_⟩
  · exact word_cost_bound _ _ _ _ _ hx hy hmLength hlen
  · simpa [hx] using padTo_length xs out
  · rw [padTo_value_of_lt, hv]
    rw [hx, hv]
    exact (Nat.mod_lt _ hm).trans_le hcapacity

theorem wordMul_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      RunsIn wordMulProgram (6000 * (B + 1) ^ 2)
        ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩
        ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨r1, out, hr, hlen, hv⟩ :=
    mulMod_value (readRegs regs 1 3 none) xs ys modulus hm
  obtain ⟨rf, ht⟩ := canonical_execute mulModProgram regs r1 xs ys modulus out
    (600 * (modulus.length + xs.length + ys.length + 1) ^ 2) hr
  refine ⟨rf, padTo xs out, ht.mono ?_, ?_, ?_⟩
  · exact word_cost_bound _ _ _ _ _ hx hy hmLength hlen
  · simpa [hx] using padTo_length xs out
  · rw [padTo_value_of_lt, hv]
    rw [hx, hv]
    exact (Nat.mod_lt _ hm).trans_le hcapacity

theorem wordAdd_primitive (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      SubexponentialSAT.Computation.RunsIn (primitive wordAddProgram).step
        (primitiveOverhead wordAddProgram * (6000 * (B + 1) ^ 2))
        (primitiveCfg wordAddProgram
          ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩)
        (primitiveCfg wordAddProgram
          ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩) ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨rf, output, ht, hlen, hv⟩ := wordAdd_value regs xs ys modulus B hx hy hmLength hm hcapacity
  exact ⟨rf, output, primitive_execution _ ht, hlen, hv⟩

theorem wordMul_primitive (regs : Fin 8 → Bool) (xs ys modulus : List Bool) (B : ℕ)
    (hx : xs.length = B) (hy : ys.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ finalRegs output,
      SubexponentialSAT.Computation.RunsIn (primitive wordMulProgram).step
        (primitiveOverhead wordMulProgram * (6000 * (B + 1) ^ 2))
        (primitiveCfg wordMulProgram
          ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput xs ys modulus) []⟩)
        (primitiveCfg wordMulProgram
          ⟨none, finalRegs, extendSeven (resting output modulus []) []⟩) ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨rf, output, ht, hlen, hv⟩ := wordMul_value regs xs ys modulus B hx hy hmLength hm hcapacity
  exact ⟨rf, output, primitive_execution _ ht, hlen, hv⟩

end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
