import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms


/-! The seven residual-entry tapes are outside every read/write footprint
of the actual producer.  This yields exact preservation, hence blankness
preservation, without changing the executable or assuming Produced fields. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.ResidualFrame
open BitProgram StructuredCalls ProgramTapeReplay

def residualTape (i : Fin 768) : Prop :=
  i ∈ ([265,301,302,303,304,305,307] : List (Fin 768))
instance : DecidablePred residualTape := fun i => inferInstanceAs
  (Decidable (i ∈ ([265,301,302,303,304,305,307] : List (Fin 768))))
def hidden : Fin 640 → Prop := residualTape ∘ wideStacks
instance : DecidablePred hidden := fun i => inferInstanceAs
  (Decidable (residualTape (wideStacks i)))

theorem visible (i : Fin 640) (h : 340 ≤ i.val) : ¬hidden i := by
  intro hh
  have hv : i.val=265 ∨ i.val=301 ∨ i.val=302 ∨ i.val=303 ∨
      i.val=304 ∨ i.val=305 ∨ i.val=307 := by
    simpa [hidden,Function.comp_def,residualTape,wideStacks,Fin.ext_iff] using hh
  omega

theorem not_touched (i : Fin 640) (hi : hidden i) :
    i∉finalDiscard ∧ i∉idempotentStartPorts ∧ i∉296::nodesStartPorts ∧
    i∉constantStartPorts := by
  have hv : i=265 ∨ i=301 ∨ i=302 ∨ i=303 ∨ i=304 ∨ i=305 ∨ i=307 := by
    simpa [hidden,Function.comp_def,residualTape,wideStacks,Fin.ext_iff] using hi
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem clear (i : Fin 640) (h : ¬hidden i) :
    AvoidsCmd hidden (LeafRingSetupProgram.clear i) :=
  avoids_clearProgram hidden i 30 31 h

theorem copy (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.copy src dst) :=
  avoids_copyProgram hidden src dst 639 30 31 hs hd (by decide)

theorem overwrite (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.overwrite src dst) :=
  ⟨clear dst hd,copy src dst hs hd⟩

theorem clearPorts (ps : List (Fin 640)) (hp : ∀i∈ps,¬hidden i) :
    AvoidsCmd hidden (LeafRingSetupProgram.clearPorts ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨clear p (hp p (by simp)),ih (fun i hi => hp i (by simp [hi]))⟩

theorem reset {r s : ℕ} (H : Fin s → Prop) (ps : List (Fin r)) :
    AvoidsCmd H (RegisterResetProgram.clear ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

theorem resetAll : AvoidsCmd hidden (RegisterResetProgram.all : Cmd 32 640) := reset _ _

theorem unary (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.unary src dst) := by
  apply avoids_call_lift_of_range
  intro i
  unfold unaryPorts
  split_ifs
  · exact hs
  · exact hd
  · apply visible
    dsimp
    omega

theorem unaryPlan (ps : List (Fin 640 × Fin 640))
    (hp : ∀p∈ps,¬hidden p.1 ∧ ¬hidden p.2) :
    AvoidsCmd hidden (LeafRingSetupProgram.unaryPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨unary p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem copyPlan (ps : List (Fin 640 × Fin 640))
    (hp : ∀p∈ps,¬hidden p.1 ∧ ¬hidden p.2) :
    AvoidsCmd hidden (LeafRingSetupProgram.copyPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨overwrite p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem number : AvoidsCmd hidden numberPhase := by
  have hc : ∀i∈workPorts++outputPorts,¬hidden i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      apply visible
      change 340 ≤ 417+j.val
      omega
    · have hh : ∀i∈outputPorts,¬hidden i := by
        intro j hj hh
        have hv : j.val=265 ∨ j.val=301 ∨ j.val=302 ∨ j.val=303 ∨
            j.val=304 ∨ j.val=305 ∨ j.val=307 := by
          simpa [hidden,Function.comp_def,residualTape,wideStacks,Fin.ext_iff] using hh
        simp [outputPorts] at hj
        omega
      exact hh i hi
  have hs : AvoidsCmd hidden serializationCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    change 340 ≤ 340+i.val
    omega
  have hu : AvoidsCmd hidden (LeafRingSetupProgram.unaryPlan numericPlan) :=
    unaryPlan _ (by
      intro p hp
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact ⟨clearPorts _ hc,hs,hu,overwrite 373 511 (by decide) (by decide),resetAll⟩

theorem core : AvoidsCmd hidden coreCommand := by
  have sc : AvoidsCmd hidden scalarCall :=
    avoids_call_lift_of_range _ _ _ _ (by decide)
  have se : AvoidsCmd hidden searchCall :=
    avoids_call_lift_of_range _ _ _ _ (by decide)
  have pa : AvoidsCmd hidden paddingCall :=
    avoids_call_lift_of_range _ _ _ _ (by decide)
  have ta : AvoidsCmd hidden tableCall :=
    avoids_call_lift_of_range _ _ _ _ (by decide)
  exact ⟨sc,overwrite 507 253 (by decide) (by decide),resetAll,
    ⟨se,overwrite 202 432 (by decide) (by decide),pa⟩,
    overwrite 498 538 (by decide) (by decide),ta⟩

theorem buildConstant (src out : Fin 640) (hs : ¬hidden src) (ho : ¬hidden out) :
    AvoidsCmd hidden (LeafRingSetupProgram.buildConstant src out) := by
  refine ⟨overwrite src 538 hs (by decide),?_⟩
  apply avoids_call_lift_of_range
  intro i
  unfold constant
  split_ifs
  · decide
  · exact ho
  · decide
  · decide
  · apply visible
    dsimp
    omega

theorem constants : AvoidsCmd hidden constantsPhase := by
  have hc : ∀i∈constantStartPorts,¬hidden i := by
    intro i hi hh
    exact (not_touched i hh).2.2.2 hi
  exact ⟨clearPorts _ hc,
    ⟨buildConstant 498 207 (by decide) (by decide),
      buildConstant 508 211 (by decide) (by decide),
      buildConstant 203 280 (by decide) (by decide)⟩,
    copyPlan _ (by
      intro p hp
      simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> decide)⟩

theorem nodes : AvoidsCmd hidden nodesPhase := by
  have hn : AvoidsCmd hidden nodesCall :=
    avoids_call_lift_of_range _ _ _ _ (by decide)
  have hf : AvoidsCmd hidden nodeFramesCall :=
    avoids_call_lift_of_range _ _ _ _ (by
      intro i hh
      have hv : (nodeFramePorts i).val=265 ∨ (nodeFramePorts i).val=301 ∨
          (nodeFramePorts i).val=302 ∨ (nodeFramePorts i).val=303 ∨
          (nodeFramePorts i).val=304 ∨ (nodeFramePorts i).val=305 ∨
          (nodeFramePorts i).val=307 := by
        simpa [hidden,Function.comp_def,residualTape,wideStacks,Fin.ext_iff] using hh
      fin_cases i <;> norm_num [nodeFramePorts] at hv)
  exact ⟨clearPorts _ (by
      intro i hi hh
      exact (not_touched i hh).2.2.1 (List.mem_cons_of_mem 296 hi)),copyPlan _ (by
      intro p hp
      simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> decide),hn,
    overwrite 256 628 (by decide) (by decide),hf,overwrite 628 256 (by decide) (by decide)⟩

theorem idempotents : AvoidsCmd hidden idempotentPhase := by
  have hc : ∀i∈idempotentStartPorts,¬hidden i := by
    intro i hi hh
    exact (not_touched i hh).2.1 hi
  have h : AvoidsCmd hidden idempotentCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    change 340 ≤ 480+i.val
    omega
  exact ⟨clearPorts _ hc,overwrite 373 511 (by decide) (by decide),resetAll,h,
    overwrite 512 281 (by decide) (by decide)⟩

theorem producerCommand_avoids : AvoidsCmd hidden producerCommand := by
  have hc : ∀i∈finalDiscard,¬hidden i := by
    intro i hi hh
    exact (not_touched i hh).1 hi
  exact ⟨number,core,constants,nodes,idempotents,clearPorts _ hc,resetAll⟩

theorem producerWideCall_avoids :
    AvoidsCmd residualTape producerWideCall :=
  avoids_liftProgram _ _ _ _ (avoids_compiled hidden producerCommand
    producerCommand_avoids (parameters 0) 300)

theorem producerWideCall_frame
    {base out : StructuredProgram.State 40 768} {n : ℕ}
    (he : Eval producerWideCall n base out)
    (i : Fin 768) (hi : residualTape i) : out.stacks i=base.stacks i := by
  have hr := eval_rebase residualTape producerWideCall_avoids he base.stacks
  have hbase : rebaseState residualTape base.stacks base=base := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      simp [rebaseStacks]
  rw [hbase] at hr
  have heq := SubexpPrimeProgram.eval_result_unique he hr 0 0
  have hs := congrArg (fun z => z.stacks i) heq
  simpa [rebaseState,rebaseStacks,hi] using hs

theorem producerWideCall_empty
    {base out : StructuredProgram.State 40 768} {n : ℕ}
    (he : Eval producerWideCall n base out)
    (i : Fin 768) (hi : residualTape i) (hz : base.stacks i=[]) :
    out.stacks i=[] := (producerWideCall_frame he i hi).trans hz

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.ResidualFrame

end OAI.Algorithms
