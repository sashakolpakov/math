import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramIncidence

namespace OAI.Algorithms

/-! Actual incidence generation never observes the seven collector tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.IncidenceTapeFootprint
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

def collectorTape (i : Fin 768) : Prop :=
  i ∈ ([256,265,301,302,303,304,305] : List (Fin 768))

instance : DecidablePred collectorTape := fun i =>
  inferInstanceAs (Decidable (i ∈ ([256,265,301,302,303,304,305] : List (Fin 768))))

private theorem safe_high (i : Fin 768) (hi : 340 ≤ i.val) : ¬ collectorTape i := by
  intro h
  simp only [collectorTape,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hi

private theorem staging_before : AvoidsCmd collectorTape SourceStaging.before := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.savePairs,collectorTape]
  · simp [SourceStaging.cachePorts,collectorTape]

private theorem staging_after : AvoidsCmd collectorTape SourceStaging.after := by
  refine ⟨avoids_clearMany _ _ ?_,avoids_copyMany _ _ _ (by decide) ?_,
    avoids_clearMany _ _ ?_,avoids_clearMany _ _ ?_⟩
  · simp [SourceStaging.cachePorts,collectorTape]
  · simp [SourceStaging.restorePairs,collectorTape]
  · simp [SourceStaging.backupPorts,collectorTape]
  · intro i hi
    obtain ⟨j,_,rfl⟩ := (SourceStaging.lowClear_iff i).mp hi
    exact safe_high _ (by change 340 ≤ 340+j.val; omega)

private theorem source_prepare : AvoidsCmd collectorTape SourceControls.prepare := by
  refine ⟨avoids_copyMany _ _ _ (by decide) ?_,trivial,by change ¬ collectorTape 365; decide⟩
  simp [SourceControls.pairs,collectorTape]

private theorem source_cleanup : AvoidsCmd collectorTape SourceControls.cleanup := by
  apply avoids_clearMany
  intro i hi
  have hh := (SourceControls.mem_extraPorts i).mp hi
  exact safe_high i (by omega)

theorem source : AvoidsCmd collectorTape Source.command := by
  refine ⟨staging_before,source_prepare,?_,staging_after,source_cleanup⟩
  apply avoids_call_lift_of_range
  intro i
  exact safe_high _ (by change 340 ≤ 340+i.val; omega)

private theorem inner (code : Cmd 16 256) :
    AvoidsCmd collectorTape (PerturbationAssembly.liftInner code) := by
  apply avoids_liftCommand_of_range
  intro i
  exact safe_high _ (by change 340 ≤ 340+i.val; omega)

theorem prepareFactor (body : Cmd 16 768) (hb : AvoidsCmd collectorTape body) :
    AvoidsCmd collectorTape (PerturbationAssembly.prepareFactor body) := by
  refine ⟨inner _,avoids_forCmd _ _ _ (by decide) ?_,inner _⟩
  exact ⟨inner _,⟨inner _,inner _,hb,inner _⟩,inner _⟩

theorem command : AvoidsCmd collectorTape Incidence.command := by
  refine ⟨?_,prepareFactor _ source,?_⟩
  · refine ⟨avoids_copyMany _ _ _ (by decide) ?_,?_,trivial,by change ¬ collectorTape 550; decide⟩
    · simp [Incidence.pairs,collectorTape]
    · exact avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)
  · refine ⟨avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide),
      avoids_clearMany _ _ ?_⟩
    intro i hi
    exact safe_high i ((Incidence.mem_workerPorts i).mp hi).1

theorem program : AvoidsProgram collectorTape Incidence.program :=
  avoids_compiled _ _ command _ _

theorem caller : AvoidsCmd collectorTape Incidence.caller :=
  avoids_liftProgram _ _ _ _ program

end SubexponentialSAT.SqrtLog.LeafProgram.IncidenceTapeFootprint

end OAI.Algorithms
