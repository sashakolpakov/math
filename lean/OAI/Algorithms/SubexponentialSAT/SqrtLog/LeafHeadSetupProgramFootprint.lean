import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFootprintStorage

namespace OAI.Algorithms

/-! The whole physical head builder avoids the indexed collector's seven
opaque tapes. The certificate covers every instruction, including calls. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage ProgramTapeReplay

theorem avoids_initializeAddress : AvoidsCmd Hidden initializeAddress :=
  avoids_stage _ _ _ _ _ (by simp [addressInputs,Hidden,carriedPorts])
    (by simp [addressOutputs,Hidden,carriedPorts])
theorem avoids_countRows : AvoidsCmd Hidden countRows :=
  avoids_stage _ _ _ _ _ (by simp [rowCountInputs,Hidden,carriedPorts])
    (by simp [rowCountOutputs,Hidden,carriedPorts])
theorem avoids_initializeCache : AvoidsCmd Hidden initializeCache :=
  avoids_stage _ _ _ _ _ (by simp [cacheInputs,Hidden,carriedPorts])
    (by simp [cacheOutputs,Hidden,carriedPorts])
theorem avoids_boot : AvoidsCmd Hidden boot :=
  ⟨avoids_initializeAddress,avoids_countRows,avoids_initializeCache⟩

theorem avoids_heads : AvoidsCmd Hidden heads :=
  avoids_stage _ _ _ _ _ (by simp [headInputs,Hidden,carriedPorts])
    (by simp [headOutputs,Hidden,carriedPorts])
theorem avoids_factors : AvoidsCmd Hidden factors :=
  avoids_stage _ _ _ _ _ (by simp [factorInputs,Hidden,carriedPorts])
    (by simp [factorOutputs,Hidden,carriedPorts])
theorem avoids_trueCount : AvoidsCmd Hidden trueCount :=
  avoids_stage _ _ _ _ _ (by simp [countInputs,Hidden,carriedPorts])
    (by simp [countOutputs,Hidden,carriedPorts])
theorem avoids_scatterSupport : AvoidsCmd Hidden scatterSupport :=
  avoids_stage _ _ _ _ _ (by simp [scatterInputs,Hidden,carriedPorts])
    (by simp [scatterOutputs,Hidden,carriedPorts])
theorem avoids_prepareHead : AvoidsCmd Hidden prepareHead :=
  ⟨avoids_heads,⟨avoids_trueCount,avoids_scatterSupport⟩,avoids_factors⟩

theorem avoids_pushConst {r : ℕ} (dst : Fin 768) (value : Fin r) (b : Bool)
    (h : ¬ Hidden dst) : AvoidsCmd Hidden (SubexponentialSAT.Subexp.TupleProgram.pushConst dst value b) :=
  ⟨trivial,h⟩

theorem avoids_tupleInit : AvoidsCmd Hidden tupleInit :=
  ⟨avoids_pushConst _ _ _ (by decide),avoids_pushConst _ _ _ (by decide),
    avoids_pushConst _ _ _ (by decide),avoids_pushConst _ _ _ (by decide)⟩
theorem avoids_appendHead : AvoidsCmd Hidden appendHead :=
  avoids_stage _ _ _ _ _ (by simp [tupleInputs,Hidden,carriedPorts])
    (by simp [tupleOutputs,Hidden,carriedPorts])
theorem avoids_finalize : AvoidsCmd Hidden finalize :=
  avoids_stage _ _ _ _ _ (by simp [finalInputs,Hidden,carriedPorts])
    (by simp [finalOutputs,Hidden,carriedPorts])

theorem avoids_matrixBuckets (entry : Cmd 16 256) : AvoidsCmd Hidden (matrixBuckets entry) :=
  avoids_stage _ _ _ _ _ (by simp [matrixInputs,Hidden,carriedPorts])
    (by simp [matrixOutputs,Hidden,carriedPorts])
theorem avoids_clearHead : AvoidsCmd Hidden clearHead :=
  avoids_clearMany Hidden _ (by simp [Hidden,carriedPorts])
theorem avoids_advanceAddress : AvoidsCmd Hidden advanceAddress :=
  avoids_pushConst _ _ _ (by decide)
theorem avoids_headStep (entry : Cmd 16 256) : AvoidsCmd Hidden (headStep entry) :=
  ⟨avoids_prepareHead,avoids_matrixBuckets entry,avoids_appendHead,avoids_clearHead,
    avoids_advanceAddress⟩
theorem avoids_headLoop (entry : Cmd 16 256) : AvoidsCmd Hidden (headLoop entry) :=
  ⟨by change ¬ Hidden (648 : Fin 768); decide,avoids_headStep entry,
    by change ¬ Hidden (648 : Fin 768); decide⟩

theorem avoids_retainCache : AvoidsCmd Hidden retainCache :=
  ⟨avoids_clearMany Hidden retainedPorts (by simp [retainedPorts,Hidden,carriedPorts]),
    avoids_copyMany Hidden temporary retainedCopies (by decide)
      (by simp [retainedCopies,Hidden,carriedPorts])⟩
theorem avoids_cleanup : AvoidsCmd Hidden cleanup := by
  apply avoids_clearMany
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact workPorts_not_hidden (by decide) i hi
  · have hr := (privatePorts_mem i).mp hi
    intro h
    simp only [Hidden,carriedPorts,List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hr

theorem avoids_command (entry : Cmd 16 256) : AvoidsCmd Hidden (LeafHeadSetupProgram.command entry) :=
  ⟨⟨avoids_boot,avoids_retainCache,avoids_tupleInit⟩,
    avoids_headLoop entry,avoids_finalize,avoids_cleanup⟩

theorem avoids_program (entry : Cmd 16 256) : AvoidsProgram Hidden (LeafHeadSetupProgram.program entry) :=
  avoids_compiled Hidden _ (avoids_command entry) _ _

theorem avoids_wideProgram (entry : Cmd 16 256) :
    AvoidsProgram Hidden (LeafHeadSetupProgram.wideProgram entry) :=
  avoids_liftProgram Hidden _ _ _ (avoids_program entry)

theorem native_avoids : AvoidsCmd Hidden Native.command := avoids_command Native.entry
theorem native_wide_avoids : AvoidsCmd Hidden (.call Native.wideProgram) :=
  avoids_wideProgram Native.entry

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Footprint

end OAI.Algorithms
