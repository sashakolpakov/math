import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpModulusShape
import OAI.Algorithms.SubexponentialSAT.PowerPrograms
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-!
# A fixed machine preparing a canonical prime-power modulus

The input words encode the base and exponent in binary. A copied exponent
drives a width-construction loop, the original drives multiplication, and the
result is normalized with the constructed shape. Every component is a fixed
Boolean-stack instruction table. Natural exponentiation appears only in the
correctness statements.
-/

namespace SubexponentialSAT.SubexpModulusMachine

open BitProgram StructuredProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Data := StructuredProgram.State 8 11

/-- Base, exponent, raw result, six work stacks, copied exponent, and the
shape port that receives the final canonical output. -/
def stackState (base exponent result copied shape : List Bool) : Fin 11 → List Bool :=
  ![base, exponent, result, [], [], [], [], [], [], copied, shape]

def state (r : Regs) (base exponent result copied shape : List Bool) : Data :=
  ⟨r, stackState base exponent result copied shape⟩

@[simp] theorem stack_exponent (base exponent result copied shape : List Bool) :
    stackState base exponent result copied shape 1 = exponent := rfl

@[simp] theorem stack_copied (base exponent result copied shape : List Bool) :
    stackState base exponent result copied shape 9 = copied := rfl

@[simp] theorem update_copied (base exponent result copied shape next : List Bool) :
    Function.update (stackState base exponent result copied shape) 9 next =
      stackState base exponent result next shape := by
  funext i
  fin_cases i <;> simp [stackState]

def shapePorts : Fin 5 → Fin 11 := ![0, 9, 10, 7, 8]
def powerPorts (i : Fin 9) : Fin 11 := ⟨i.val, by omega⟩
def normalizePorts : Fin 3 → Fin 11 := ![10, 2, 4]

theorem shapePorts_injective : Function.Injective shapePorts := by decide
theorem powerPorts_injective : Function.Injective powerPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 11 => k.val) h
theorem normalizePorts_injective : Function.Injective normalizePorts := by decide

private theorem embed_ports {s : ℕ} (port : Fin s → Fin 11)
    (hinj : Function.Injective port) (r rf : Regs)
    (localStk : Fin s → List Bool) (frame target : Fin 11 → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedState id port (⟨r, frame⟩ : Data) ⟨rf, localStk⟩ = ⟨rf, target⟩ := by
  apply CounterForPrograms.data_ext
  · simp [embedState]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack id port _ _ hinj j).trans (hport j).symm
    · exact (embedState_stack_frame id port _ _ i hi).trans (hframe i hi).symm

theorem embed_shape (r rf : Regs) (base exponent result counter shape : List Bool) :
    embedState id shapePorts (state r base exponent result [] [])
      (SubexpModulusShape.state rf base counter shape) =
        state rf base exponent result counter shape := by
  apply embed_ports shapePorts shapePorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ (9 : Fin 11) := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ (10 : Fin 11) := fun h => hi ⟨2, h.symm⟩
    fin_cases i <;> simp_all [stackState]

theorem embed_power (r rf : Regs)
    (base frameExponent exponent result copied shape : List Bool) :
    embedState id powerPorts (state r base frameExponent [] copied shape)
      (PowerPrograms.state rf base exponent result) =
        state rf base exponent result copied shape := by
  apply embed_ports powerPorts powerPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hlarge : 9 ≤ i.val := by
      by_contra h
      have hsmall : i.val < 9 := by omega
      exact hi ⟨⟨i.val, hsmall⟩, Fin.ext rfl⟩
    fin_cases i <;> simp_all [stackState]

theorem embed_normalize (r rf : Regs) (base exponent result copied shape : List Bool) :
    embedState id normalizePorts (state r base exponent [] copied [])
      ⟨rf, ModularPrograms.operandStacks shape result []⟩ =
        state rf base exponent result copied shape := by
  apply embed_ports normalizePorts normalizePorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h2 : i ≠ (2 : Fin 11) := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ (10 : Fin 11) := fun h => hi ⟨0, h.symm⟩
    fin_cases i <;> simp_all [stackState]

abbrev saveCounter : StructuredCalls.Cmd 8 11 :=
  .call (StackRoutines.copyProgram 1 9 8 0 1)

abbrev buildShape : StructuredCalls.Cmd 8 11 :=
  .call (ProgramLinking.liftProgram SubexpModulusShape.program id shapePorts)

abbrev computePower : StructuredCalls.Cmd 8 11 :=
  .call (ProgramLinking.liftProgram PowerPrograms.program id powerPorts)

abbrev normalizeResult : StructuredCalls.Cmd 8 11 :=
  .call (ProgramLinking.liftProgram ModularPrograms.paddingLEProgram id normalizePorts)

theorem saveCounter_eval (r : Regs) (base exponent : List Bool) :
    StructuredCalls.Eval saveCounter (7 * exponent.length + 5)
      (state r base exponent [] [] [])
      (state (readRegs r 0 1 none) base exponent [] exponent []) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.copyProgram_trace (1 : Fin 11) 9 8 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) r
    (stackState base exponent [] [] []) rfl
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [state, StackRoutines.copyResult, StackRoutines.copyStacks] using hh

theorem buildShape_eval (r : Regs) (base exponent : List Bool) :
    ∃ n rf copied shape,
      n ≤ SubexpModulusShape.runtimeBound base exponent ∧
      StructuredCalls.Eval buildShape n (state r base exponent [] exponent [])
        (state rf base exponent [] copied shape) ∧
      shape.length = 1 + BinaryArithmetic.toNat exponent * base.length ∧
      BinaryArithmetic.toNat copied = 0 ∧ copied.length = exponent.length := by
  obtain ⟨rf, copied, shape, hl, hz, hw, n, hn, ht⟩ :=
    SubexpModulusShape.run_width r base exponent
  have he := eval_call_lifted SubexpModulusShape.program id shapePorts
    (state r base exponent [] [] []) Function.injective_id shapePorts_injective ht
  refine ⟨n, rf, copied, shape, hn, ?_, hl, hz, hw⟩
  simpa only [embed_shape] using he

theorem computePower_eval (r : Regs) (base exponent copied shape : List Bool) :
    ∃ n rf remaining result,
      n ≤ PowerPrograms.runtimeBound base exponent ∧
      StructuredCalls.Eval computePower n (state r base exponent [] copied shape)
        (state rf base remaining result copied shape) ∧
      BinaryArithmetic.toNat result = BinaryArithmetic.toNat base ^ BinaryArithmetic.toNat exponent ∧
      result.length ≤ 1 + BinaryArithmetic.toNat exponent * base.length ∧
      BinaryArithmetic.toNat remaining = 0 ∧ remaining.length = exponent.length := by
  obtain ⟨d, hv, hl, hb, hz, hw, hs, n, hn, ht⟩ := PowerPrograms.run_value r base exponent
  have hd : d = PowerPrograms.state d.regs base (d.stacks 1) (d.stacks 2) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i
      · exact hb
      · rfl
      · rfl
      all_goals exact hs _ (by decide)
  rw [hd] at ht
  have he := eval_call_lifted PowerPrograms.program id powerPorts
    (state r base exponent [] copied shape) Function.injective_id powerPorts_injective ht
  refine ⟨n, d.regs, d.stacks 1, d.stacks 2, hn, ?_, hv, hl, hz, hw⟩
  simpa only [embed_power] using he

theorem normalizeResult_eval (r : Regs) (base exponent result copied shape : List Bool)
    (hlen : result.length ≤ shape.length) :
    ∃ n rf, n ≤ 7 * shape.length + 6 ∧
      StructuredCalls.Eval normalizeResult n (state r base exponent result copied shape)
        (state rf base exponent [] copied (ModularArithmetic.padTo shape result)) := by
  obtain ⟨rf, ht, _⟩ := ModularPrograms.paddingLE_correct r shape result hlen
  have he := eval_call_lifted ModularPrograms.paddingLEProgram id normalizePorts
    (state r base exponent [] copied []) Function.injective_id normalizePorts_injective
    (a := ⟨r, ModularPrograms.operandStacks shape result []⟩)
    (b := ⟨rf, ModularPrograms.operandStacks (ModularArithmetic.padTo shape result) [] []⟩) ht
  refine ⟨7 * shape.length + 6, rf, le_rfl, ?_⟩
  simpa only [embed_normalize] using he

abbrev command : StructuredCalls.Cmd 8 11 :=
  .seq saveCounter (.seq buildShape (.seq computePower normalizeResult))

/-- One instruction table for all bases and binary exponents. -/
def program := StructuredCalls.compiled command (0 : Fin 11) 10

theorem command_size : StructuredCalls.size command = 147 := by
  change 8 + ((StructuredCalls.size SubexpModulusShape.command + 1) +
    ((StructuredCalls.size PowerPrograms.command + 1) + 9)) = 147
  rw [SubexpModulusShape.command_size, PowerPrograms.command_size]

def runtimeBound (base exponent : List Bool) : ℕ :=
  7 * exponent.length + SubexpModulusShape.runtimeBound base exponent +
    PowerPrograms.runtimeBound base exponent + 7 * (1 + BinaryArithmetic.toNat exponent * base.length) + 12

/-- The measured bound is a polynomial in the exponent value and the two
encoded input lengths. In particular no output value occurs in this bound. -/
theorem runtimeBound_eq (base exponent : List Bool) :
    runtimeBound base exponent =
      BinaryArithmetic.toNat exponent * (50 * (base.length + 1) *
        (2 + (BinaryArithmetic.toNat exponent + 1) * base.length)) +
      BinaryArithmetic.toNat exponent * (7 * base.length + 5) +
      2 * (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) +
      7 * (1 + BinaryArithmetic.toNat exponent * base.length) + 7 * exponent.length + 18 := by
  simp only [runtimeBound, SubexpModulusShape.runtimeBound, PowerPrograms.runtimeBound,
    PowerPrograms.workBound, PowerPrograms.callbackBound]
  ring

/-- The canonical output agrees with the source-level construction, and the
bound counts the actual finite program including its final halt. -/
theorem run_powerRun (r : Regs) (base exponent : List Bool) :
    ∃ rf remaining copied,
      BinaryArithmetic.toNat remaining = 0 ∧ remaining.length = exponent.length ∧
      BinaryArithmetic.toNat copied = 0 ∧ copied.length = exponent.length ∧
      BitProgram.RunsIn program (runtimeBound base exponent)
        ((state r base exponent [] [] []).withPC (some program.entry))
        ((state rf base remaining [] copied
          (SubexpModulusConstruction.powerRun base (BinaryArithmetic.toNat exponent)).1).withPC none) := by
  obtain ⟨ns, rs, copied, shape, hns, hes, hshape, hcz, hcl⟩ :=
    buildShape_eval (readRegs r 0 1 none) base exponent
  obtain ⟨np, rp, remaining, result, hnp, hep, hv, hl, hrz, hrl⟩ :=
    computePower_eval rs base exponent copied shape
  have hlen : result.length ≤ shape.length := by omega
  obtain ⟨nn, rn, hnn, hen⟩ := normalizeResult_eval rp base remaining result copied shape hlen
  have hout : ModularArithmetic.padTo shape result =
      (SubexpModulusConstruction.powerRun base (BinaryArithmetic.toNat exponent)).1 := by
    apply SubexpModulusConstruction.bits_eq_of_length_of_value
    · rw [ModularArithmetic.padTo_length, SubexpModulusConstruction.powerRun_length, hshape]
    · rw [ModularArithmetic.padTo_correct shape result hlen,
        SubexpModulusConstruction.powerRun_value, hv]
  have he := StructuredCalls.Eval.seq (saveCounter_eval r base exponent)
    (StructuredCalls.Eval.seq hes (StructuredCalls.Eval.seq hep hen))
  rw [hout] at he
  refine ⟨rn, remaining, copied, hrz, hrl, hcz, hcl,
    (7 * exponent.length + 5) + (ns + (np + nn)) + 1, ?_,
    StructuredCalls.compiled_halt_trace he 0 10⟩
  dsimp [runtimeBound]
  omega

theorem primitive_powerRun (r : Regs) (base exponent : List Bool) :
    ∃ rf remaining copied,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound base exponent)
        (BitProgram.primitiveCfg program
          ((state r base exponent [] [] []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program ((state rf base remaining [] copied
          (SubexpModulusConstruction.powerRun base (BinaryArithmetic.toNat exponent)).1).withPC none)) := by
  obtain ⟨rf, remaining, copied, _, _, _, _, ht⟩ := run_powerRun r base exponent
  exact ⟨rf, remaining, copied, BitProgram.primitive_execution program ht⟩

/-- Prime-power preparation needs only the encoded base and exponent.
Primality is unnecessary for this arithmetic operation. -/
theorem run_modulus (r : Regs) (p μ : ℕ) (base exponent : List Bool)
    (hbase : BinaryArithmetic.toNat base = p) (hexponent : BinaryArithmetic.toNat exponent = μ)
    (hwidth : base.length = Nat.log 2 p + 1) :
    ∃ rf remaining copied,
      BitProgram.RunsIn program (runtimeBound base exponent)
        ((state r base exponent [] [] []).withPC (some program.entry))
        ((state rf base remaining [] copied
          (SubexpLiftRing.fixedBits (SubexpLiftRing.baseWidth p μ + 1) (p ^ μ))).withPC none) := by
  obtain ⟨rf, remaining, copied, _, _, _, _, ht⟩ := run_powerRun r base exponent
  refine ⟨rf, remaining, copied, ?_⟩
  rw [hexponent, SubexpModulusConstruction.modulus_eq_fixedBits p μ base hbase hwidth] at ht
  exact ht

theorem primitive_modulus (r : Regs) (p μ : ℕ) (base exponent : List Bool)
    (hbase : BinaryArithmetic.toNat base = p) (hexponent : BinaryArithmetic.toNat exponent = μ)
    (hwidth : base.length = Nat.log 2 p + 1) :
    ∃ rf remaining copied,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound base exponent)
        (BitProgram.primitiveCfg program
          ((state r base exponent [] [] []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program ((state rf base remaining [] copied
          (SubexpLiftRing.fixedBits (SubexpLiftRing.baseWidth p μ + 1) (p ^ μ))).withPC none)) := by
  obtain ⟨rf, remaining, copied, ht⟩ := run_modulus r p μ base exponent hbase hexponent hwidth
  exact ⟨rf, remaining, copied, BitProgram.primitive_execution program ht⟩

end SubexponentialSAT.SubexpModulusMachine

end OAI.Algorithms
