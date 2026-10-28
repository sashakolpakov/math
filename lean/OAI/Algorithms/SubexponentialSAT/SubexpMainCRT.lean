import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTCore
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterProgram

namespace OAI.Algorithms

/-!
# Concrete CRT phase assembly

The fixed preparation and scratch-clear programs surround the actual finite
CRT controller. Only the controller's measured execution trace remains an
explicit integration premise; no semantic CRT instruction is introduced.
-/

namespace SubexponentialSAT.SubexpMainCRT

open BitProgram StructuredCalls SubexpMainProgram

def crt (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 320
  labels := size SubexpCRTOuterProgram.command + 1
  program := SubexpCRTOuterProgram.program
  register := register er
  stack := ⟨fun i => stackMap alloc (i.castAdd 10),
    (stackMap_injective alloc).comp (Fin.castAdd_injective 320 10)⟩

theorem crt_project {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (crt er alloc).project a = projectCRT alloc a := rfl

theorem prepared_input {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 7) :
    (preparedData alloc a).stacks (persistent es (inputIndex i)) =
      a.stacks (persistent es (inputIndex i)) := by
  have h := embedState_stack (preparation er alloc).registerMap (preparation er alloc).stack
    a (SubexpCRTPreparation.result ((preparation er alloc).project a))
    (preparation er alloc).stack.injective (SubexpCRTPreparation.inputPort i)
  have hh := h.trans (SubexpCRTPreparation.result_input ((preparation er alloc).project a) i)
  change (preparedData alloc a).stacks (stackMap alloc (SubexpCRTPreparation.inputPort i)) =
    a.stacks (stackMap alloc (SubexpCRTPreparation.inputPort i)) at hh
  simpa only [stackMap_input] using hh

theorem crt_input_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin 7) :
    ((crt er alloc).install a out).stacks (persistent es (inputIndex i)) =
      a.stacks (persistent es (inputIndex i)) := by
  apply embedState_stack_frame (crt er alloc).registerMap (crt er alloc).stack a out
    (persistent es (inputIndex i))
  rintro ⟨j, hj⟩
  change stackMap alloc (j.castAdd 10) = persistent es (inputIndex i) at hj
  rw [← stackMap_input alloc i] at hj
  have hv := congrArg Fin.val (stackMap_injective alloc hj)
  change j.val = 320 + i.val at hv
  have hjlt : j.val < 320 := j.isLt
  omega

theorem phase_input {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin 7) :
    (finalData alloc ((crt er alloc).install (preparedData alloc a) out)).stacks
        (persistent es (inputIndex i)) = a.stacks (persistent es (inputIndex i)) := by
  have hb := alloc.enough.trans alloc.within
  have hi : 7 ≤ (persistent es (inputIndex i)).val := by simp [persistent]; omega
  rw [finalData_high_frame alloc _ _ hi, crt_input_frame, prepared_input]

theorem phase_output {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) :
    (finalData alloc ((crt er alloc).install (preparedData alloc a) out)).stacks
      (persistent es 10) = out.stacks 261 := by
  have hi : 7 ≤ (persistent es 10).val := by simp [persistent]
  rw [finalData_high_frame alloc _ _ hi]
  have h := embedState_stack (crt er alloc).registerMap (crt er alloc).stack
    (preparedData alloc a) out (crt er alloc).stack.injective (261 : Fin 320)
  change ((crt er alloc).install (preparedData alloc a) out).stacks
    (stackMap alloc 261) = out.stacks 261 at h
  simpa only [stackMap_output] using h

theorem crt_low_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin (totalStacks es)) (hi : i.val < 256) :
    ((crt er alloc).install a out).stacks i = a.stacks i := by
  apply embedState_stack_frame (crt er alloc).registerMap (crt er alloc).stack a out i
  rintro ⟨j, hj⟩
  have hl := stackMap_lower_bound alloc (j.castAdd 10)
  have hv := congrArg Fin.val hj
  change (stackMap alloc (j.castAdd 10)).val = i.val at hv
  omega

/-- The disjoint preparation and CRT bank leave the decoder's five scratch
words unchanged until the measured epilogue clears them. -/
theorem scratchBits_after_crt {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) :
    scratchBits alloc ((crt er alloc).install (preparedData alloc a) out) =
      scratchBits alloc a := by
  have h (i : Fin 640) (hi : i.val < 256) :
      ((crt er alloc).install (preparedData alloc a) out).stacks (ordinary alloc i) =
        a.stacks (ordinary alloc i) :=
    (crt_low_frame alloc _ out _ hi).trans (prepared_low_frame alloc a _ hi)
  simp only [scratchBits, h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 6 (by decide)]

theorem epilogueBound_after_crt {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) :
    epilogueBound alloc ((crt er alloc).install (preparedData alloc a) out) =
      2 * scratchBits alloc a + 16 := by
  rw [epilogueBound_eq, scratchBits_after_crt]

/-- The source-ring caches, at ordinary128..137, survive the entire phase.
The stronger interval statement also frames every other lower work port
except the five decoder scratch locations. -/
theorem phase_low_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin (totalStacks es))
    (hlo : 7 ≤ i.val) (hhi : i.val < 256) :
    (finalData alloc ((crt er alloc).install (preparedData alloc a) out)).stacks i =
      a.stacks i := by
  rw [finalData_high_frame alloc _ i hlo, crt_low_frame alloc _ out i hhi,
    prepared_low_frame alloc a i hhi]

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (preparation er alloc)
    (SubexpProcedureCompose.sequence (crt er alloc) (epilogue er alloc))

/-- The preparation and decoder-scratch epilogue are proved here. The middle
premise is an actual trace of the fixed CRT controller, not a semantic oracle. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) {t : ℕ}
    (hcrt : Trace SubexpCRTOuterProgram.program t
      (((crt er alloc).project (preparedData alloc a)).withPC
        (some SubexpCRTOuterProgram.program.entry)) (out.withPC none)) :
    ∃ n, Eval (procedure er alloc).invoke n a
      (finalData alloc ((crt er alloc).install (preparedData alloc a) out)) ∧
      n ≤ preparationBound alloc a + t +
        epilogueBound alloc ((crt er alloc).install (preparedData alloc a) out) + 2 := by
  obtain ⟨n, hn, hp⟩ := preparation_execution alloc a
  have hc := Procedure.invoke_trace (crt er alloc) (preparedData alloc a) out hcrt
  have he := epilogue_execution alloc ((crt er alloc).install (preparedData alloc a) out)
  refine ⟨n + (t + epilogueBound alloc ((crt er alloc).install (preparedData alloc a) out) + 1) + 1,
    SubexpProcedureCompose.sequence_invoke _ _ hp
      (SubexpProcedureCompose.sequence_invoke _ _ hc he), ?_⟩
  omega

/-- A bound using only the actual CRT count and words present before this
phase. In particular, the unread leaf stream is absent. -/
theorem execution_bound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) {t : ℕ}
    (hcrt : Trace SubexpCRTOuterProgram.program t
      (((crt er alloc).project (preparedData alloc a)).withPC
        (some SubexpCRTOuterProgram.program.entry)) (out.withPC none)) :
    ∃ n, Eval (procedure er alloc).invoke n a
      (finalData alloc ((crt er alloc).install (preparedData alloc a) out)) ∧
      n ≤ preparationBound alloc a + t + 2 * scratchBits alloc a + 18 := by
  obtain ⟨n, hn, hb⟩ := execution alloc a out hcrt
  rw [epilogueBound_after_crt] at hb
  exact ⟨n, hn, by omega⟩

end SubexponentialSAT.SubexpMainCRT

end OAI.Algorithms
