import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFootprintStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried

namespace OAI.Algorithms

/-! The head builder never reads or writes the enclosing marked/residual
loop's arbitrary carried tapes320,322,332. Every call is checked by its
actual relocated bank; no local service footprint is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.FootprintOuterCarried
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage ProgramTapeReplay
open Footprint (avoids_prepare avoids_finish avoids_clearMany avoids_copyMany)

theorem work_not_hidden {s : ℕ} (hs : s ≤ 288) (i : Fin s) : ¬ LeafProgram.OuterCarried.hidden (workPort hs i) := by
  intro h
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with h|h|h <;>
    have hv := congrArg Fin.val h <;>
    norm_num [workPort] at hv <;> omega

theorem workPorts_not_hidden {s : ℕ} (hs : s ≤ 288) : ∀ i∈workPorts hs,¬ LeafProgram.OuterCarried.hidden i := by
  intro i hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
  exact work_not_hidden hs j

theorem avoids_stage {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hs : s ≤ 288) (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (hi : ∀ q∈ins,¬ LeafProgram.OuterCarried.hidden q.1) (ho : ∀ q∈outs,¬ LeafProgram.OuterCarried.hidden q.2) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (stage p reg hs ins outs) := by
  have ht : ¬ LeafProgram.OuterCarried.hidden temporary := by decide
  have hin : ∀ q∈inputCopies hs ins,¬ LeafProgram.OuterCarried.hidden q.1 ∧ ¬ LeafProgram.OuterCarried.hidden q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨hi z hz,work_not_hidden hs z.2⟩
  have hout : ∀ q∈outputCopies hs outs,¬ LeafProgram.OuterCarried.hidden q.1 ∧ ¬ LeafProgram.OuterCarried.hidden q.2 := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    exact ⟨work_not_hidden hs z.1,ho z hz⟩
  exact ⟨avoids_prepare LeafProgram.OuterCarried.hidden temporary (workPorts hs) (inputCopies hs ins)
      ht (workPorts_not_hidden hs) hin,
    avoids_liftProgram_of_range LeafProgram.OuterCarried.hidden p reg (workPort hs) (work_not_hidden hs),
    avoids_finish LeafProgram.OuterCarried.hidden temporary (workPorts hs) (outputCopies hs outs)
      ht (workPorts_not_hidden hs) hout⟩

theorem avoids_initializeAddress : AvoidsCmd LeafProgram.OuterCarried.hidden initializeAddress :=
  avoids_stage _ _ _ _ _ (by simp [addressInputs,LeafProgram.OuterCarried.hidden])
    (by simp [addressOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_countRows : AvoidsCmd LeafProgram.OuterCarried.hidden countRows :=
  avoids_stage _ _ _ _ _ (by simp [rowCountInputs,LeafProgram.OuterCarried.hidden])
    (by simp [rowCountOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_initializeCache : AvoidsCmd LeafProgram.OuterCarried.hidden initializeCache :=
  avoids_stage _ _ _ _ _ (by simp [cacheInputs,LeafProgram.OuterCarried.hidden])
    (by simp [cacheOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_boot : AvoidsCmd LeafProgram.OuterCarried.hidden boot :=
  ⟨avoids_initializeAddress,avoids_countRows,avoids_initializeCache⟩

theorem avoids_heads : AvoidsCmd LeafProgram.OuterCarried.hidden heads :=
  avoids_stage _ _ _ _ _ (by simp [headInputs,LeafProgram.OuterCarried.hidden])
    (by simp [headOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_factors : AvoidsCmd LeafProgram.OuterCarried.hidden factors :=
  avoids_stage _ _ _ _ _ (by simp [factorInputs,LeafProgram.OuterCarried.hidden])
    (by simp [factorOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_trueCount : AvoidsCmd LeafProgram.OuterCarried.hidden trueCount :=
  avoids_stage _ _ _ _ _ (by simp [countInputs,LeafProgram.OuterCarried.hidden])
    (by simp [countOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_scatterSupport : AvoidsCmd LeafProgram.OuterCarried.hidden scatterSupport :=
  avoids_stage _ _ _ _ _ (by simp [scatterInputs,LeafProgram.OuterCarried.hidden])
    (by simp [scatterOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_prepareHead : AvoidsCmd LeafProgram.OuterCarried.hidden prepareHead :=
  ⟨avoids_heads,⟨avoids_trueCount,avoids_scatterSupport⟩,avoids_factors⟩

theorem avoids_pushConst {r : ℕ} (dst : Fin 768) (value : Fin r) (b : Bool)
    (h : ¬ LeafProgram.OuterCarried.hidden dst) : AvoidsCmd LeafProgram.OuterCarried.hidden (SubexponentialSAT.Subexp.TupleProgram.pushConst dst value b) :=
  ⟨trivial,h⟩

theorem avoids_tupleInit : AvoidsCmd LeafProgram.OuterCarried.hidden tupleInit :=
  ⟨avoids_pushConst _ _ _ (by decide),avoids_pushConst _ _ _ (by decide),
    avoids_pushConst _ _ _ (by decide),avoids_pushConst _ _ _ (by decide)⟩
theorem avoids_appendHead : AvoidsCmd LeafProgram.OuterCarried.hidden appendHead :=
  avoids_stage _ _ _ _ _ (by simp [tupleInputs,LeafProgram.OuterCarried.hidden])
    (by simp [tupleOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_finalize : AvoidsCmd LeafProgram.OuterCarried.hidden finalize :=
  avoids_stage _ _ _ _ _ (by simp [finalInputs,LeafProgram.OuterCarried.hidden])
    (by simp [finalOutputs,LeafProgram.OuterCarried.hidden])

theorem avoids_matrixBuckets (entry : Cmd 16 256) : AvoidsCmd LeafProgram.OuterCarried.hidden (matrixBuckets entry) :=
  avoids_stage _ _ _ _ _ (by simp [matrixInputs,LeafProgram.OuterCarried.hidden])
    (by simp [matrixOutputs,LeafProgram.OuterCarried.hidden])
theorem avoids_clearHead : AvoidsCmd LeafProgram.OuterCarried.hidden clearHead :=
  avoids_clearMany LeafProgram.OuterCarried.hidden _ (by simp [LeafProgram.OuterCarried.hidden])
theorem avoids_advanceAddress : AvoidsCmd LeafProgram.OuterCarried.hidden advanceAddress :=
  avoids_pushConst _ _ _ (by decide)
theorem avoids_headStep (entry : Cmd 16 256) : AvoidsCmd LeafProgram.OuterCarried.hidden (headStep entry) :=
  ⟨avoids_prepareHead,avoids_matrixBuckets entry,avoids_appendHead,avoids_clearHead,
    avoids_advanceAddress⟩
theorem avoids_headLoop (entry : Cmd 16 256) : AvoidsCmd LeafProgram.OuterCarried.hidden (headLoop entry) :=
  ⟨by change ¬ LeafProgram.OuterCarried.hidden (648 : Fin 768); decide,avoids_headStep entry,
    by change ¬ LeafProgram.OuterCarried.hidden (648 : Fin 768); decide⟩

theorem avoids_retainCache : AvoidsCmd LeafProgram.OuterCarried.hidden retainCache :=
  ⟨avoids_clearMany LeafProgram.OuterCarried.hidden retainedPorts (by simp [retainedPorts,LeafProgram.OuterCarried.hidden]),
    avoids_copyMany LeafProgram.OuterCarried.hidden temporary retainedCopies (by decide)
      (by simp [retainedCopies,LeafProgram.OuterCarried.hidden])⟩
theorem avoids_cleanup : AvoidsCmd LeafProgram.OuterCarried.hidden cleanup := by
  apply avoids_clearMany
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact workPorts_not_hidden (by decide) i hi
  · have hr := (privatePorts_mem i).mp hi
    intro h
    simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hr

theorem avoids_command (entry : Cmd 16 256) : AvoidsCmd LeafProgram.OuterCarried.hidden (LeafHeadSetupProgram.command entry) :=
  ⟨⟨avoids_boot,avoids_retainCache,avoids_tupleInit⟩,
    avoids_headLoop entry,avoids_finalize,avoids_cleanup⟩

theorem avoids_program (entry : Cmd 16 256) : AvoidsProgram LeafProgram.OuterCarried.hidden (LeafHeadSetupProgram.program entry) :=
  avoids_compiled LeafProgram.OuterCarried.hidden _ (avoids_command entry) _ _

theorem avoids_wideProgram (entry : Cmd 16 256) :
    AvoidsProgram LeafProgram.OuterCarried.hidden (LeafHeadSetupProgram.wideProgram entry) :=
  avoids_liftProgram LeafProgram.OuterCarried.hidden _ _ _ (avoids_program entry)

theorem native_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Native.command := avoids_command Native.entry
theorem native_wide_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden (.call Native.wideProgram) :=
  avoids_wideProgram Native.entry

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.FootprintOuterCarried

end OAI.Algorithms
