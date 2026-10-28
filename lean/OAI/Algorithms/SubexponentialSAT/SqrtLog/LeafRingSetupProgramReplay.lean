import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

def hidden : Fin 640 → Prop := LeafProgram.OuterCarried.hidden ∘ wideStacks
instance : DecidablePred hidden := fun i => inferInstanceAs
  (Decidable (LeafProgram.OuterCarried.hidden (wideStacks i)))

theorem hidden_bounds {i : Fin 640} (h : hidden i) : 320 ≤ i.val ∧ i.val < 340 := by
  have hv : i.val=320 ∨ i.val=322 ∨ i.val=332 := by
    simpa [hidden,Function.comp_def,LeafProgram.OuterCarried.hidden,wideStacks,
      Fin.ext_iff] using h
  omega

theorem visible (i : Fin 640) (h : i.val < 320 ∨ 340 ≤ i.val) : ¬hidden i := by
  intro hh
  have := hidden_bounds hh
  omega

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
    right
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
      right
      change 340 ≤ 417+j.val
      omega
    · have hh : ∀i∈outputPorts,¬hidden i := by
        intro j hj
        apply visible
        left
        simp [outputPorts] at hj
        omega
      exact hh i hi
  have hs : AvoidsCmd hidden serializationCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
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
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (scalar_avoids_collector i))
  have se : AvoidsCmd hidden searchCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (search_avoids_collector i))
  have pa : AvoidsCmd hidden paddingCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (search_avoids_collector i))
  have ta : AvoidsCmd hidden tableCall :=
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (table_avoids_collector i))
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
    right
    dsimp
    omega

theorem constants : AvoidsCmd hidden constantsPhase := by
  have hc : ∀i∈constantStartPorts,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).2.2.2.1 hi
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
    avoids_call_lift_of_range _ _ _ _ (fun i => visible _ (nodes_avoids_collector i))
  have hf : AvoidsCmd hidden nodeFramesCall :=
    avoids_call_lift_of_range _ _ _ _ (by
      intro i
      apply visible
      left
      fin_cases i <;> norm_num [nodeFramePorts])
  exact ⟨clearPorts _ (by
      intro i hi
      apply visible
      simp [nodesStartPorts] at hi
      omega),copyPlan _ (by
      intro p hp
      simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> decide),hn,
    overwrite 256 628 (by decide) (by decide),hf,overwrite 628 256 (by decide) (by decide)⟩

theorem idempotents : AvoidsCmd hidden idempotentPhase := by
  have hc : ∀i∈idempotentStartPorts,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).2.1 hi
  have h : AvoidsCmd hidden idempotentCall := by
    apply avoids_call_lift_of_range
    intro i
    apply visible
    right
    change 340 ≤ 480+i.val
    omega
  exact ⟨clearPorts _ hc,overwrite 373 511 (by decide) (by decide),resetAll,h,
    overwrite 512 281 (by decide) (by decide)⟩

theorem producerCommand_avoids : AvoidsCmd hidden producerCommand := by
  have hc : ∀i∈finalDiscard,¬hidden i := by
    intro i hi hh
    have h := hidden_bounds hh
    exact (collector_not_touched i h.1 h.2).1 hi
  exact ⟨number,core,constants,nodes,idempotents,clearPorts _ hc,resetAll⟩

theorem producerWideCall_avoids :
    AvoidsCmd LeafProgram.OuterCarried.hidden producerWideCall :=
  avoids_liftProgram _ _ _ _ (avoids_compiled hidden producerCommand
    producerCommand_avoids (parameters 0) 300)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
