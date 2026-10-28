import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatPrepare
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatFrame

namespace OAI.Algorithms

/-!
# Flat-record quartic multiplication by an actual fixed Boolean-stack program

Preparation, the 49-operation word-bank multiplier, packing, and cleanup are
all executed by finite instruction tables. The prime, exponent, modulus,
reduction coefficients, and operand bits are runtime data.
-/

namespace SubexponentialSAT.SubexpQuarticFlatMul

open BitProgram StackRoutines StructuredCalls
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

theorem bankStore_native (bank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) (i : Fin 70) :
    bankStore bank modulus reduction width output (bankPorts i) =
      SubexpQuarticMachine.store bank (SubexpQuarticMachine.scalarWork [] [] modulus) [] i := by
  refine Fin.addCases (m := 61) (n := 9) (fun j => ?_) (fun j => ?_) i
  · change bankStore bank modulus reduction width output (Fin.castAdd 16 j) =
      SubexpQuarticMachine.store bank (SubexpQuarticMachine.scalarWork [] [] modulus) []
        (SubexpQuarticMachine.bankPort j)
    simp
  · fin_cases j <;> simp [bankStore, bankPorts, SubexpQuarticMachine.store,
      SubexpQuarticMachine.scalarWork, Fin.addCases]
    all_goals rfl

theorem embed_bank {B : ℕ} (regs frameRegs : Fin 8 → Bool)
    (bank : Fin 61 → Word B) (frameBank : Fin 61 → List Bool)
    (modulus reduction width output : List Bool) :
    embedState id bankPorts ⟨frameRegs, bankStore frameBank modulus reduction width output⟩
      (SubexpQuarticMachine.restingState regs bank modulus) =
      ⟨regs, bankStore (fun i => (bank i).val) modulus reduction width output⟩ := by
  apply SubexpScanPrimitives.embedState_eq id bankPorts Function.injective_id bankPorts.injective
  · intro i; rfl
  · intro i
    simpa only [SubexpQuarticMachine.restingState] using
      (bankStore_native (fun j => (bank j).val) modulus reduction width output i)
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have hn : ¬ j.val < 70 := by
      intro h
      exact hj ⟨⟨j.val, h⟩, rfl⟩
    have hb : ¬ j.val < 61 := by omega
    simp [bankStore, hb]

abbrev bankCallCmd : Cmd 8 77 :=
  .call (ProgramLinking.liftProgram SubexpQuarticMachine.mulProgram id bankPorts)

theorem bankCall_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (bank : Fin 61 → Word (baseWidth p μ)) (regs : Fin 8 → Bool)
    (reduction width : List Bool) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool),
      n ≤ (49 * 6100 + 1) * (baseWidth p μ + 1)^2 ∧
      Eval bankCallCmd n
        ⟨regs, bankStore (fun i => (bank i).val) M.bits reduction width []⟩
        ⟨finalRegs, bankStore
          (fun i => (SubexpQuarticMachine.scriptEval p μ M SubexpQuarticMachine.mulCode bank i).val)
          M.bits reduction width []⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpQuarticMachine.mul_program_run p μ M regs bank
  have h := eval_call_lifted SubexpQuarticMachine.mulProgram id bankPorts
    (⟨regs, bankStore (fun i => (bank i).val) M.bits reduction width []⟩ : State 8 77)
    Function.injective_id bankPorts.injective ht
  refine ⟨n, rf, hn, ?_⟩
  simpa only [bankCallCmd, embed_bank] using h

abbrev command : Cmd 8 77 := .seq prepareCmd (.seq bankCallCmd finishCmd)

/-- The program is independent of every arithmetic parameter. -/
abbrev program : Program 8 77 (size command + 1) := compiled command 70 72

theorem program_size : size command + 1 = 8954 := by
  norm_num [command, bankCallCmd, size, prepareCmd_size, finishCmd_size,
    SubexpQuarticMachine.mulProgram_size]

theorem command_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool), n + 1 ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval command n ⟨regs, initialStore M.bits width t a b⟩
        ⟨finalRegs, finalStore M.bits width t (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩ := by
  have hp := prepare_eval t a b M.bits width hw regs
  obtain ⟨n, rf, hn, hb⟩ := bankCall_eval p μ M (initialBank t a b)
    (readRegs regs 0 1 none) (flat t) width
  have hf := finish_eval
    (SubexpQuarticMachine.scriptEval p μ M SubexpQuarticMachine.mulCode (initialBank t a b))
    M.bits (flat t) width rf
  have hout : SubexpQuarticMachine.mulOutput
      (SubexpQuarticMachine.scriptEval p μ M SubexpQuarticMachine.mulCode (initialBank t a b)) =
      (SubexpPreparedQuartic.binaryMul p μ M t a b).1 := by
    simpa only [initialBank_reduction, initialBank_left, initialBank_right] using
      SubexpQuarticMachine.mulCode_correct p μ M (initialBank t a b)
  rw [hout] at hf
  refine ⟨n + 689 * baseWidth p μ + 591, readRegs rf 0 1 none, ?_, ?_⟩
  · nlinarith [Nat.zero_le (baseWidth p μ), Nat.zero_le ((baseWidth p μ)^2)]
  · have total := hp.seq (hb.seq hf)
    have htime : (539 * baseWidth p μ + 385) + (n + (150 * baseWidth p μ + 206)) =
        n + 689 * baseWidth p μ + 591 := by omega
    rw [htime] at total
    exact total

/-- Complete measured execution, including every setup/copy/cleanup step. -/
theorem program_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (400000 * (baseWidth p μ + 1)^2)
        ⟨some program.entry, regs, initialStore M.bits width t a b⟩
        ⟨none, finalRegs, finalStore M.bits width t (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩ := by
  obtain ⟨n, rf, hn, he⟩ := command_run p μ M t a b width hw regs
  refine ⟨rf, n + 1, hn, ?_⟩
  exact compiled_halt_trace he 70 72

/-- The actual primitive execution proposition, with the finite program kept
abstract while the dependent configuration types are checked. -/
abbrev PrimitiveRunsIn {r s l : ℕ} (P : Program r s l) (steps : ℕ)
    (a b : Cfg r s l) : Prop :=
  Computation.RunsIn (primitive P).step steps (primitiveCfg P a) (primitiveCfg P b)

theorem primitiveRunsIn_of_runsIn {r s l : ℕ} (P : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (h : RunsIn P steps a b) :
    PrimitiveRunsIn P (primitiveOverhead P * steps) a b :=
  BitProgram.primitive_execution P h

theorem program_primitive (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ))) (width : List Bool)
    (hw : width.length = baseWidth p μ) (regs : Fin 8 → Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      PrimitiveRunsIn program
        (primitiveOverhead program * (400000 * (baseWidth p μ + 1)^2))
        ⟨some program.entry, regs, initialStore M.bits width t a b⟩
        ⟨none, finalRegs, finalStore M.bits width t (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩ := by
  obtain ⟨rf, hr⟩ := program_run p μ M t a b width hw regs
  exact ⟨rf, primitiveRunsIn_of_runsIn program hr⟩

@[simp] theorem final_modulus {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) :
    finalStore modulus width t result 66 = modulus := by simp [finalStore]

@[simp] theorem final_reduction {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) :
    finalStore modulus width t result 73 = flat t := by simp [finalStore]

@[simp] theorem final_width {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) :
    finalStore modulus width t result 74 = width := by simp [finalStore]

@[simp] theorem final_output {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) :
    finalStore modulus width t result 72 = flat result := by simp [finalStore]

theorem final_empty {B : ℕ} (modulus width : List Bool) (t result : Quad (Word B)) (j : Fin 77)
    (hm : j ≠ 66) (ho : j ≠ 72) (hr : j ≠ 73) (hw : j ≠ 74) :
    finalStore modulus width t result j = [] := by
  by_cases hj : j.val < 61 <;> simp [finalStore, bankStore, hj, hm, ho, hr, hw]


end SubexponentialSAT.SubexpQuarticFlatMul

end OAI.Algorithms
