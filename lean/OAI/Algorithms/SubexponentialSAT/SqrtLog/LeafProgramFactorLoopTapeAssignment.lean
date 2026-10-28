import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopTapeBase

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem setupMove (src dst : Fin 768) (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (LeafAssignmentSetupProgram.move src dst) :=
  ⟨transfer src 359 0 1 hs (by decide),transfer 359 dst 0 1 (by decide) hd⟩

theorem setupBefore : AvoidsCmd collectorTape LeafAssignmentSetupProgram.beforeCommand := by
  have hm : AvoidsCmd collectorTape LeafAssignmentSetupProgram.mergeCommand :=
    liftProgram _ _ _ (by decide)
  have hw : AvoidsCmd collectorTape LeafAssignmentSetupProgram.weightCommand :=
    liftProgram _ _ _ (by decide)
  exact ⟨setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),hm,hw⟩

theorem setupAfter : AvoidsCmd collectorTape LeafAssignmentSetupProgram.afterCommand :=
  ⟨clear _ 0 1 (by decide),clear _ 0 1 (by decide),
    setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),
    setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),
    clear _ 0 1 (by decide),clear _ 0 1 (by decide)⟩

theorem factorMove (src dst : Fin 768) (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (Factor.move src dst) :=
  ⟨copy src dst 159 0 1 hs hd (by decide),clear src 0 1 hs⟩

theorem factorID : AvoidsCmd collectorTape FactorID.command :=
  ⟨copy 149 556 359 0 1 (by decide) (by decide) (by decide),by change ¬collectorTape 556; decide⟩

theorem dispatch : AvoidsCmd collectorTape FactorDispatch.command := by
  have hd : AvoidsCmd collectorTape FactorDispatch.dispatch := liftProgram _ _ _ (by decide)
  exact ⟨⟨copy 149 152 359 0 1 (by decide) (by decide) (by decide),by change ¬collectorTape 706; decide⟩,hd⟩

theorem expansion : AvoidsCmd collectorTape Expansion.forwardCommand :=
  ⟨reverse 154 358 359 0 1 (by decide) (by decide) (by decide),liftProgram _ _ _ (by decide)⟩

theorem clause : AvoidsCmd collectorTape Clause.caller := liftProgram _ _ _ (by decide)

theorem indicator : AvoidsCmd collectorTape Factor.indicator :=
  ⟨by trivial,liftProgram _ _ _ (by decide)⟩

theorem multiply : AvoidsCmd collectorTape Factor.multiply := liftProgram _ _ _ (by decide)

theorem accumulate : AvoidsCmd collectorTape Factor.accumulate :=
  ⟨factorMove _ _ (by decide) (by decide),factorMove _ _ (by decide) (by decide),multiply,
    factorMove _ _ (by decide) (by decide)⟩

theorem hashFactor (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.hashFactor :=
  ⟨⟨factorID,hi⟩,expansion,indicator,clear _ 0 1 (by decide),clear _ 0 1 (by decide),accumulate⟩

theorem markedFactor (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.markedFactor :=
  ⟨⟨factorID,hi⟩,factorMove _ _ (by decide) (by decide),clause,clear _ 0 1 (by decide),accumulate⟩

theorem callback (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.callback :=
  ⟨dispatch,⟨hashFactor hi,markedFactor hi,by trivial⟩,clear _ 0 1 (by decide),by trivial⟩

theorem factorLoop (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.loop := records Factor.ports _ (by decide) (by decide) (callback hi)

theorem factorCommand (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.command :=
  ⟨copy _ _ 159 0 1 (by decide) (by decide) (by decide),
    copy _ _ 159 0 1 (by decide) (by decide) (by decide),factorLoop hi,
    factorMove _ _ (by decide) (by decide)⟩

theorem assignment (hi : AvoidsCmd collectorTape Incidence.caller) :
    AvoidsCmd collectorTape Factor.assignment := ⟨setupBefore,factorCommand hi,setupAfter⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape

end OAI.Algorithms
