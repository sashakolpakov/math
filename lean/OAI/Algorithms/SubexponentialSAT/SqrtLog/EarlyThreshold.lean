import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative

namespace OAI.Algorithms

/-! A paid, fixed native producer of the early high-incidence threshold.
The source is the original ambient count in bank slot 0.  It is never replaced
by the residual count or by the later block-size parameter. -/

namespace SubexponentialSAT.SqrtLog.EarlyThreshold

open BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank LeafParametersProgram.Circuit


def threshold (ambient : ℕ) : ℕ := Nat.sqrt (Asymptotic.L ambient) + 1

theorem threshold_ge_two (ambient : ℕ) : 2 ≤ threshold ambient := by
  have := Nat.sqrt_pos.mpr (Asymptotic.L_pos ambient)
  unfold threshold
  omega

theorem log_lt_threshold_sq (ambient : ℕ) :
    Asymptotic.L ambient < threshold ambient ^ 2 :=
  Nat.lt_succ_sqrt' (Asymptotic.L ambient)

/-- The only modified public words are 13 and 16.  The arithmetic operations
already include their concrete bit-level implementation and scratch cleanup. -/
def code : List Instr := [
  .clear 13, .copy 0 13 (by decide), .addConst 13 16, .logSucc 13,
  .clear 16, .sqrt 13 16 (by decide), .addConst 16 1]

abbrev command : Cmd 8 77 := LeafParametersProgram.Circuit.program code

theorem admissible (m : Model) : AdmissibleCode code m := by
  simp [code, AdmissibleCode, Admissible, next, output, value, lengthBound]

theorem result_log (m : Model) :
    (result code m).val 13 = Asymptotic.L (m.val 0) := by
  simp [code, result, next, value, output, Asymptotic.L]

theorem result_threshold (m : Model) :
    (result code m).val 16 = threshold (m.val 0) := by
  simp [code, result, next, value, output, threshold, Asymptotic.L]

theorem result_log_length (m : Model) :
    (result code m).len 13 = m.len 0 + 17 := by
  simp [code, result, next, lengthBound, output, Nat.add_assoc]

theorem result_threshold_length (m : Model) :
    (result code m).len 16 = Asymptotic.L (m.val 0) + 1 := by
  simp [code, result, next, lengthBound, value, output, Asymptotic.L]

/-- Strengthening of the circuit execution lemma with exact preservation of
every word outside the instruction's destination. -/
theorem instruction_shape_frame (m : Model) (w : Words) (r : Regs)
    (hs : Shape m w) (i : Instr) (hi : Admissible m i) :
    ∃ t rf w', Eval (LeafParametersProgram.Circuit.command i) t
      (state r w) (state rf w') ∧ Shape (next m i) w' ∧
      t ≤ cost m.val m.len i ∧ ∀ a, a ≠ output i → w' a = w a := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    instruction_eval i r w (shape_ready m w hs i hi)
  have hval : values w = m.val := funext hs.1
  rw [hval] at hv hl ht
  have hl' := hl.trans (lengthBound_mono m.val (lengths w) m.len hs.2 i)
  have ht' := ht.trans (cost_mono m.val (lengths w) m.len hs.2 i)
  refine ⟨t, rf, Function.update w (output i) word, he, ⟨?_, ?_⟩, ht', ?_⟩
  · intro a
    by_cases ha : a = output i
    · subst a; simpa [next] using hv
    · simpa [next, ha] using hs.1 a
  · intro a
    by_cases ha : a = output i
    · subst a; simpa [next] using hl'
    · simpa [next, ha] using hs.2 a
  · intro a ha
    simp [ha]

theorem circuit_eval_frame (is : List Instr) (m : Model) (w : Words) (r : Regs)
    (hs : Shape m w) (hi : AdmissibleCode is m) :
    ∃ t rf w', Eval (LeafParametersProgram.Circuit.program is) t
      (state r w) (state rf w') ∧ Shape (result is m) w' ∧
      t ≤ budget is m ∧
      ∀ a, (∀ i ∈ is, output i ≠ a) → w' a = w a := by
  induction is generalizing m w r with
  | nil => exact ⟨0, r, w, .base (.skip _), hs, le_rfl, fun _ _ => rfl⟩
  | cons i is ih =>
    obtain ⟨t, rf, w', he, hs', ht, hf⟩ := instruction_shape_frame m w r hs i hi.1
    obtain ⟨u, rg, w'', he', hs'', hu, hf'⟩ := ih (next m i) w' rf hs' hi.2
    refine ⟨t + u, rg, w'', he.seq he', hs'', Nat.add_le_add ht hu, ?_⟩
    intro a ha
    rw [hf' a (fun j hj => ha j (List.mem_cons_of_mem i hj))]
    exact hf a (Ne.symm (ha i List.mem_cons_self))

theorem output_ne (a : Fin 64) (h13 : a ≠ 13) (h16 : a ≠ 16) :
    ∀ i ∈ code, output i ≠ a := by
  simp [code, output, Ne.symm h13, Ne.symm h16]

theorem execution (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (state r w) (state rf w') ∧
      Shape (result code m) w' ∧ t ≤ budget code m ∧
      BinaryArithmetic.toNat (w' 13) = Asymptotic.L (m.val 0) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (m.val 0) ∧
      ∀ a, a ≠ 13 → a ≠ 16 → w' a = w a := by
  obtain ⟨t, rf, w', he, hs', ht, hf⟩ :=
    circuit_eval_frame code m w r hs (admissible m)
  refine ⟨t, rf, w', he, hs', ht, ?_, ?_, ?_⟩
  · exact (hs'.1 13).trans (result_log m)
  · exact (hs'.1 16).trans (result_threshold m)
  · intro a h13 h16
    exact hf a (output_ne a h13 h16)

/-- This expression charges both clears, copying, the binary logarithm,
binary square root, and both additions. -/
theorem budget_eq (m : Model) :
    budget code m =
      2 * m.len 13 + 2 * m.len 16 + 7 * m.len 0 +
      128 * (m.len 0 + 17) + 32 * (m.len 0 + 17)^2 +
      200001 * (Asymptotic.L (m.val 0) + m.len 0 + 19)^3 +
      8 * (Asymptotic.L (m.val 0) + 2) + 23 := by
  simp [code, budget, next, output, cost, value, lengthBound, Asymptotic.L]
  ring

def sizeBound (m : Model) : ℕ :=
  m.len 0 + m.len 13 + m.len 16 + Asymptotic.L (m.val 0) + 20

theorem budget_le (m : Model) : budget code m ≤ 300000 * sizeBound m ^ 3 := by
  let B := sizeBound m
  have hB : 1 ≤ B := by dsimp [B, sizeBound]; omega
  have h1 : 1 ≤ B^3 := Nat.one_le_pow _ _ hB
  have hB3 : B ≤ B^3 := by
    have hh : B^1 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
    simpa using hh
  have hB2 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  rw [budget_eq]
  calc
    _ ≤ 2 * B + 2 * B + 7 * B + 128 * B + 32 * B^2 + 200001 * B^3 + 8 * B + 23 := by
      gcongr <;> dsimp [B, sizeBound] <;> omega
    _ ≤ 300000 * B^3 := by omega

def program := compiled command (port 0) (port 16)

theorem program_runs (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ rf w', RunsIn program (budget code m + 1)
      ((state r w).withPC (some program.entry)) ((state rf w').withPC none) ∧
      Shape (result code m) w' ∧
      BinaryArithmetic.toNat (w' 13) = Asymptotic.L (m.val 0) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (m.val 0) ∧
      ∀ a, a ≠ 13 → a ≠ 16 → w' a = w a := by
  obtain ⟨t, rf, w', he, hs', ht, hl, hv, hf⟩ := execution m w r hs
  exact ⟨rf, w', ⟨t + 1, Nat.add_le_add_right ht 1,
    compiled_halt_trace he (port 0) (port 16)⟩, hs', hl, hv, hf⟩

theorem primitive_execution (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ rf w', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (budget code m + 1))
      (primitiveCfg program ((state r w).withPC (some program.entry)))
      (primitiveCfg program ((state rf w').withPC none)) ∧
      Shape (result code m) w' ∧
      BinaryArithmetic.toNat (w' 13) = Asymptotic.L (m.val 0) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (m.val 0) ∧
      ∀ a, a ≠ 13 → a ≠ 16 → w' a = w a := by
  obtain ⟨rf, w', he, hs', hl, hv, hf⟩ := program_runs m w r hs
  exact ⟨rf, w', BitProgram.primitive_execution program he, hs', hl, hv, hf⟩

/-- The standard isolated input bank contains only the original ambient
binary word.  Padding zero bits is allowed. -/
def inputWords (ambient : List Bool) : Words := fun a => if a = 0 then ambient else []

def inputModel (ambient : List Bool) : Model :=
  ⟨values (inputWords ambient), lengths (inputWords ambient)⟩

theorem input_shape (ambient : List Bool) : Shape (inputModel ambient) (inputWords ambient) :=
  ⟨fun _ => rfl, fun _ => le_rfl⟩

def runtimeBound (ambient : List Bool) : ℕ :=
  300001 * (ambient.length + Asymptotic.L (BinaryArithmetic.toNat ambient) + 20)^3

theorem input_budget_le (ambient : List Bool) :
    budget code (inputModel ambient) + 1 ≤ runtimeBound ambient := by
  have hb := budget_le (inputModel ambient)
  have h1 : 1 ≤ (ambient.length + Asymptotic.L (BinaryArithmetic.toNat ambient) + 20)^3 :=
    Nat.one_le_pow _ _ (by omega)
  simpa [inputModel, sizeBound, values, lengths, inputWords, runtimeBound] using
    (show budget code (inputModel ambient) + 1 ≤
      300001 * sizeBound (inputModel ambient)^3 by
      have h1' : 1 ≤ sizeBound (inputModel ambient)^3 := by
        simpa [inputModel, sizeBound, values, lengths, inputWords] using h1
      omega)

theorem input_execution (ambient : List Bool) (r : Regs) :
    ∃ t rf w', Eval command t (state r (inputWords ambient)) (state rf w') ∧
      t + 1 ≤ runtimeBound ambient ∧
      BinaryArithmetic.toNat (w' 13) = Asymptotic.L (BinaryArithmetic.toNat ambient) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (BinaryArithmetic.toNat ambient) ∧ w' 0 = ambient ∧
      (w' 13).length ≤ ambient.length + 17 ∧
      (w' 16).length ≤ Asymptotic.L (BinaryArithmetic.toNat ambient) + 1 ∧
      ∀ a, a ≠ 0 → a ≠ 13 → a ≠ 16 → w' a = [] := by
  obtain ⟨t, rf, w', he, hs', ht, hl, hv, hf⟩ :=
    execution (inputModel ambient) (inputWords ambient) r (input_shape ambient)
  have hlen13 := hs'.2 13
  have hlen16 := hs'.2 16
  rw [result_log_length] at hlen13
  rw [result_threshold_length] at hlen16
  refine ⟨t, rf, w', he, (Nat.add_le_add_right ht 1).trans (input_budget_le ambient),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [inputModel, values, inputWords] using hl
  · simpa [inputModel, values, inputWords] using hv
  · simpa [inputWords] using hf 0 (by decide) (by decide)
  · simpa [inputModel, lengths, inputWords] using hlen13
  · simpa [inputModel, values, inputWords] using hlen16
  · intro a ha h13 h16
    simpa [inputWords, ha] using hf a h13 h16

theorem input_program_runs (ambient : List Bool) (r : Regs) :
    ∃ rf w', RunsIn program (runtimeBound ambient)
      ((state r (inputWords ambient)).withPC (some program.entry))
      ((state rf w').withPC none) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (BinaryArithmetic.toNat ambient) ∧ w' 0 = ambient ∧
      ∀ a, a ≠ 0 → a ≠ 13 → a ≠ 16 → w' a = [] := by
  obtain ⟨t, rf, w', he, ht, _, hv, hf, _, _, hz⟩ := input_execution ambient r
  exact ⟨rf, w', ⟨t + 1, ht, compiled_halt_trace he (port 0) (port 16)⟩, hv, hf, hz⟩

theorem input_primitive_execution (ambient : List Bool) (r : Regs) :
    ∃ rf w', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound ambient)
      (primitiveCfg program ((state r (inputWords ambient)).withPC (some program.entry)))
      (primitiveCfg program ((state rf w').withPC none)) ∧
      BinaryArithmetic.toNat (w' 16) = threshold (BinaryArithmetic.toNat ambient) ∧ w' 0 = ambient ∧
      ∀ a, a ≠ 0 → a ≠ 13 → a ≠ 16 → w' a = [] := by
  obtain ⟨rf, w', he, hv, hf, hz⟩ := input_program_runs ambient r
  exact ⟨rf, w', BitProgram.primitive_execution program he, hv, hf, hz⟩

end SubexponentialSAT.SqrtLog.EarlyThreshold

end OAI.Algorithms
