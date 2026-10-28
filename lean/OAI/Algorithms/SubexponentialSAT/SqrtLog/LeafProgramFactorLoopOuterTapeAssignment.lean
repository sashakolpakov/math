import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopOuterTapeBase

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem setupMove (src dst : Fin 768) (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (LeafAssignmentSetupProgram.move src dst) :=
  ⟨transfer src 359 0 1 hs (by decide),transfer 359 dst 0 1 (by decide) hd⟩

theorem setupBefore : AvoidsCmd OuterCarried.hidden LeafAssignmentSetupProgram.beforeCommand := by
  have hm : AvoidsCmd OuterCarried.hidden LeafAssignmentSetupProgram.mergeCommand :=
    liftProgram _ _ _ (by decide)
  have hw : AvoidsCmd OuterCarried.hidden LeafAssignmentSetupProgram.weightCommand :=
    liftProgram _ _ _ (by decide)
  exact ⟨setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),hm,hw⟩

theorem setupAfter : AvoidsCmd OuterCarried.hidden LeafAssignmentSetupProgram.afterCommand :=
  ⟨clear _ 0 1 (by decide),clear _ 0 1 (by decide),
    setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),
    setupMove _ _ (by decide) (by decide),setupMove _ _ (by decide) (by decide),
    clear _ 0 1 (by decide),clear _ 0 1 (by decide)⟩

theorem factorMove (src dst : Fin 768) (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (Factor.move src dst) :=
  ⟨copy src dst 159 0 1 hs hd (by decide),clear src 0 1 hs⟩

theorem factorID : AvoidsCmd OuterCarried.hidden FactorID.command :=
  ⟨copy 149 556 359 0 1 (by decide) (by decide) (by decide),by change ¬OuterCarried.hidden 556; decide⟩

theorem dispatch : AvoidsCmd OuterCarried.hidden FactorDispatch.command := by
  have hd : AvoidsCmd OuterCarried.hidden FactorDispatch.dispatch := liftProgram _ _ _ (by decide)
  exact ⟨⟨copy 149 152 359 0 1 (by decide) (by decide) (by decide),by change ¬OuterCarried.hidden 706; decide⟩,hd⟩

theorem expansion : AvoidsCmd OuterCarried.hidden Expansion.forwardCommand :=
  ⟨reverse 154 358 359 0 1 (by decide) (by decide) (by decide),liftProgram _ _ _ (by decide)⟩

theorem clause : AvoidsCmd OuterCarried.hidden Clause.caller := liftProgram _ _ _ (by decide)

theorem indicator : AvoidsCmd OuterCarried.hidden Factor.indicator :=
  ⟨by trivial,liftProgram _ _ _ (by decide)⟩

theorem multiply : AvoidsCmd OuterCarried.hidden Factor.multiply := liftProgram _ _ _ (by decide)

theorem accumulate : AvoidsCmd OuterCarried.hidden Factor.accumulate :=
  ⟨factorMove _ _ (by decide) (by decide),factorMove _ _ (by decide) (by decide),multiply,
    factorMove _ _ (by decide) (by decide)⟩

theorem hashFactor (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.hashFactor :=
  ⟨⟨factorID,hi⟩,expansion,indicator,clear _ 0 1 (by decide),clear _ 0 1 (by decide),accumulate⟩

theorem markedFactor (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.markedFactor :=
  ⟨⟨factorID,hi⟩,factorMove _ _ (by decide) (by decide),clause,clear _ 0 1 (by decide),accumulate⟩

theorem callback (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.callback :=
  ⟨dispatch,⟨hashFactor hi,markedFactor hi,by trivial⟩,clear _ 0 1 (by decide),by trivial⟩

theorem factorLoop (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.loop := records Factor.ports _ (by decide) (by decide) (callback hi)

theorem factorCommand (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.command :=
  ⟨copy _ _ 159 0 1 (by decide) (by decide) (by decide),
    copy _ _ 159 0 1 (by decide) (by decide) (by decide),factorLoop hi,
    factorMove _ _ (by decide) (by decide)⟩

theorem assignment (hi : AvoidsCmd OuterCarried.hidden Incidence.caller) :
    AvoidsCmd OuterCarried.hidden Factor.assignment := ⟨setupBefore,factorCommand hi,setupAfter⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape

end OAI.Algorithms
