import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence

namespace OAI.Algorithms

/-! Actual incidence generation never observes the three outer caller tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem safe_high (i : Fin 768) (hi : 340 ≤ i.val) : ¬ hidden i := by
  intro h
  simp only [hidden,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl <;> norm_num at hi

private theorem staging_before : AvoidsCmd hidden SourceStaging.before := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.savePairs,hidden]
  · simp [SourceStaging.cachePorts,hidden]

private theorem staging_after : AvoidsCmd hidden SourceStaging.after := by
  refine ⟨avoids_clearMany _ _ ?_,avoids_copyMany _ _ _ (by decide) ?_,
    avoids_clearMany _ _ ?_,avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.cachePorts,hidden]
  · simp [SourceStaging.restorePairs,hidden]
  · simp [SourceStaging.backupPorts,hidden]
  · intro i hi
    obtain ⟨j,_,rfl⟩ := (SourceStaging.lowClear_iff i).mp hi
    exact safe_high _ (by change 340 ≤ 340+j.val; omega)

private theorem source_prepare : AvoidsCmd hidden SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,trivial,by change ¬ hidden 365; decide⟩
  simp [SourceControls.pairs,hidden]

private theorem source_cleanup : AvoidsCmd hidden SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact safe_high i (by omega)

theorem source_avoids : AvoidsCmd hidden Source.command := by
  refine ⟨staging_before,source_prepare,?_,staging_after,source_cleanup⟩
  apply avoids_call_lift_of_range
  intro i
  exact safe_high _ (by change 340 ≤ 340+i.val; omega)

private theorem inner (code : Cmd 16 256) :
    AvoidsCmd hidden (PerturbationAssembly.liftInner code) := by
  apply avoids_liftCommand_of_range
  intro i
  exact safe_high _ (by change 340 ≤ 340+i.val; omega)

theorem incidence_prepareFactor (body : Cmd 16 768) (hb : AvoidsCmd hidden body) :
    AvoidsCmd hidden (PerturbationAssembly.prepareFactor body) := by
  refine ⟨inner _,avoids_forCmd _ _ _ (by decide) ?_,inner _⟩
  exact ⟨inner _,⟨inner _,inner _,hb,inner _⟩,inner _⟩

theorem incidence_command : AvoidsCmd hidden Incidence.command := by
  refine ⟨?_,incidence_prepareFactor _ source_avoids,?_⟩
  · refine ⟨avoids_copyMany _ _ _ (by decide) ?_,?_,trivial,by change ¬ hidden 550; decide⟩
    · simp [Incidence.pairs,hidden]
    · exact avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)
  · refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide),
      avoids_clearMany _ _ ?_⟩
    intro i hi
    exact safe_high i ((Incidence.mem_workerPorts i).mp hi).1

theorem incidence_program : AvoidsProgram hidden Incidence.program :=
  avoids_compiled _ _ incidence_command _ _

theorem incidence_caller : AvoidsCmd hidden Incidence.caller :=
  avoids_liftProgram _ _ _ _ incidence_program

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
