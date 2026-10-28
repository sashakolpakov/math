import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawIDTransport
import OAI.Algorithms.SubexponentialSAT.SubexpMainRawIDTransportPorts
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawPrefix

namespace OAI.Algorithms

/-!
# The physical raw-ID transport in the Main input ABI

The input stack is reused by the actual two-pass transport. Its only output
is then physically copied back and the temporary output is cleared. The
endpoint is the exact all-zero-register, single-input-stack Main state.
-/

namespace SubexponentialSAT.SubexpMainRawIDTransport

open BitProgram StructuredCalls SubexpMainProgram
open Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

def procedure (er es : ℕ) : Procedure er es where
  registers := 10
  stackCount := 24
  labels := size SubexpRawIDTransport.command + 1
  program := SubexpRawIDTransport.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (workRegs er) => k.val) h)⟩
  stack := ⟨stackMap es, stackMap_injective es⟩

def command (er es : ℕ) : MainCmd er es :=
  .seq (procedure er es).invoke (moveOutput er es)

def program (er es : ℕ) := compiled (command er es) (persistent es 0) (persistent es 0)

theorem project_initial (er es : ℕ) (raw : List Bool) :
    (procedure er es).project (initialData er es raw) =
      (StructuredProgram.ioState (23 : Fin 24) raw : StructuredProgram.State 10 24) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    change Fin 24 at i
    change (if stackMap es i = persistent es 0 then raw else []) =
      (if i = 23 then raw else [])
    simp only [← stackMap_raw es, (stackMap_injective es).eq_iff]

theorem install_output (er es : ℕ) (raw output : List Bool) :
    (procedure er es).install (initialData er es raw)
        (StructuredProgram.ioState (8 : Fin 24) output) =
      StructuredProgram.ioState (ordinary es 8) output := by
  apply SubexpScanPrimitives.embedState_eq _ _ (procedure er es).registerMap_injective
    (procedure er es).stack.injective
  · intro i; rfl
  · intro i
    change Fin 24 at i
    change (if stackMap es i = ordinary es 8 then output else []) =
      (if i = 8 then output else [])
    simp only [← stackMap_output es, (stackMap_injective es).eq_iff]
  · intro i hi; rfl
  · intro i hi
    have hraw : i ≠ persistent es 0 := by
      rintro rfl
      exact hi ⟨(23 : Fin 24), rfl⟩
    have hout : i ≠ ordinary es 8 := by
      rintro rfl
      exact hi ⟨(8 : Fin 24), rfl⟩
    simp [StructuredProgram.ioState, initialData, hraw, hout]

theorem execution (er es : ℕ) (F : RawIdEncoding.Formula) :
    ∃ n, Eval (command er es) n (initialData er es (RawIdEncoding.encode F))
      (initialData er es (RawIdRenaming.outputWord F)) ∧
      n + 1 ≤ 41000 * ((RawIdEncoding.encode F).length + 1)^6 := by
  obtain ⟨n, hn, ht⟩ := SubexpRawIDTransport.polynomial_runs F
  have hrun : Trace (procedure er es).program n
      (((procedure er es).project (initialData er es (RawIdEncoding.encode F))).withPC
        (some (procedure er es).program.entry))
      ((StructuredProgram.ioState (8 : Fin 24) (RawIdRenaming.outputWord F)).withPC none) := by
    rw [project_initial]
    change Trace SubexpRawIDTransport.program n
      ((StructuredProgram.ioState (23 : Fin 24) (RawIdEncoding.encode F)).withPC
        (some SubexpRawIDTransport.program.entry)) _
    have hinitial :
        (StructuredProgram.ioState (23 : Fin 24) (RawIdEncoding.encode F)).withPC
            (some SubexpRawIDTransport.program.entry) =
          initial SubexpRawIDTransport.program (RawIdEncoding.encode F) := by
      apply congrArg₂ (BitProgram.Cfg.mk (some SubexpRawIDTransport.program.entry))
      · rfl
      · funext i
        fin_cases i <;> rfl
    rw [hinitial]
    exact ht
  have he := Procedure.invoke_trace (procedure er es)
    (initialData er es (RawIdEncoding.encode F))
    (StructuredProgram.ioState (8 : Fin 24) (RawIdRenaming.outputWord F)) hrun
  rw [install_output] at he
  have hm := moveOutput_eval er es (RawIdRenaming.outputWord F)
  refine ⟨n + (9 * (RawIdRenaming.outputWord F).length + 8), he.seq hm, ?_⟩
  have ho := RawIdRenaming.output_length_le F
  have hpow : ((RawIdEncoding.encode F).length + 1)^3 ≤
      ((RawIdEncoding.encode F).length + 1)^6 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 1 ≤ ((RawIdEncoding.encode F).length + 1)^6 :=
    Nat.one_le_pow _ _ (by omega)
  omega

theorem output_eq_ordered (F : RawIdEncoding.Formula) :
    RawIdRenaming.outputWord F =
      SubexpOrderedRawPrefix.encode (RawIdRenaming.physicalRows F) := by
  rw [SubexpOrderedRawPrefix.encode_eq, RawIdRenaming.physicalRows_codes]
  rfl

/-- This is the exact preprocessing premise of the ordered Main runtime. -/
theorem ordered_execution (er es : ℕ) (F : RawIdEncoding.Formula) :
    ∃ n, Eval (command er es) n (initialData er es (RawIdEncoding.encode F))
      (initialData er es (SubexpOrderedRawPrefix.encode (RawIdRenaming.physicalRows F))) ∧
      n + 1 ≤ 41000 * ((RawIdEncoding.encode F).length + 1)^6 := by
  simpa only [output_eq_ordered] using execution er es F

theorem ordered_size (F : RawIdEncoding.Formula) :
    SubexpOrderedRawPrefix.bitLength (RawIdRenaming.physicalRows F) + 1 ≤
      17 * ((RawIdEncoding.encode F).length + 1)^3 := by
  have ho := RawIdRenaming.output_length_le F
  have hpos : 1 ≤ ((RawIdEncoding.encode F).length + 1)^3 :=
    Nat.one_le_pow _ _ (by omega)
  rw [output_eq_ordered] at ho
  change (SubexpOrderedRawPrefix.encode _).length + 1 ≤ _
  omega

theorem program_runsIn (er es : ℕ) (F : RawIdEncoding.Formula) :
    RunsIn (program er es) (41000 * ((RawIdEncoding.encode F).length + 1)^6)
      (initial (program er es) (RawIdEncoding.encode F))
      ((initialData er es (RawIdRenaming.outputWord F)).withPC none) := by
  obtain ⟨n, he, hn⟩ := execution er es F
  exact ⟨n + 1, hn, compiled_halt_trace he (persistent es 0) (persistent es 0)⟩

theorem primitive_execution (er es : ℕ) (F : RawIdEncoding.Formula) :
    Computation.RunsIn (primitive (program er es)).step
      (primitiveOverhead (program er es) *
        (41000 * ((RawIdEncoding.encode F).length + 1)^6))
      (primitiveCfg (program er es) (initial (program er es) (RawIdEncoding.encode F)))
      (primitiveCfg (program er es)
        ((initialData er es (RawIdRenaming.outputWord F)).withPC none)) :=
  BitProgram.primitive_execution _ (program_runsIn er es F)

end SubexponentialSAT.SubexpMainRawIDTransport

end OAI.Algorithms
