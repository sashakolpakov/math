import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopOuterTapeBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReadout

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem assemblyClear (src : Fin 768) (hs : ¬OuterCarried.hidden src) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.clear src) := clear src 0 1 hs

theorem assemblyCopy (src dst : Fin 768) (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.copy src dst) := copy src dst 179 0 1 hs hd (by decide)

theorem assemblyTransfer (src dst : Fin 768) (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.transfer src dst) := transfer src dst 0 1 hs hd

theorem assemblyTake (src dst : Fin 768) (hne : src≠164)
    (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (takeFrame src dst hne) :=
  ⟨reader _ hs (by change ¬OuterCarried.hidden 164; decide),assemblyTransfer 164 dst (by decide) hd⟩

theorem assemblyMove (src dst : Fin 768) (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (moveForward src dst) :=
  ⟨assemblyTransfer src 164 hs (by decide),assemblyTransfer 164 dst (by decide) hd⟩

theorem assemblyScan (src : Fin 768) (body : Code)
    (hs : ¬OuterCarried.hidden src) (hb : AvoidsCmd OuterCarried.hidden body) :
    AvoidsCmd OuterCarried.hidden (rawScan src body) := ⟨hs,hb,hs⟩

theorem weighted : AvoidsCmd OuterCarried.hidden weightedAdd :=
  liftCommand _ _ _ _ _ (by decide)

theorem product : AvoidsCmd OuterCarried.hidden multiply :=
  liftProgram _ _ _ (by decide)

theorem normalization : AvoidsCmd OuterCarried.hidden normalize :=
  liftCommand _ _ _ _ _ (by decide)

theorem projection : AvoidsCmd OuterCarried.hidden project :=
  liftCommand _ _ _ _ _ (by decide)

theorem readout : AvoidsCmd OuterCarried.hidden MomentsAssembly.readout :=
  liftProgram _ _ _ (by decide)

theorem assignmentScan (produce : Code) (hp : AvoidsCmd OuterCarried.hidden produce) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.assignmentScan produce) := by
  apply assemblyScan _ _ (by decide)
  exact ⟨assemblyTake _ _ _ (by decide) (by decide),hp,weighted,assemblyClear _ (by decide)⟩

theorem headScan (produce : Code) (hp : AvoidsCmd OuterCarried.hidden produce) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.headScan produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd OuterCarried.hidden startHead :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide),
      assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide)⟩
  have hfinish : AvoidsCmd OuterCarried.hidden finishHead :=
    ⟨assemblyMove _ _ (by decide) (by decide),product,assemblyMove _ _ (by decide) (by decide),
      assemblyClear _ (by decide),assemblyClear _ (by decide),assemblyClear _ (by decide)⟩
  exact ⟨hstart,assignmentScan produce hp,hfinish⟩

theorem supportScan (produce : Code) (hp : AvoidsCmd OuterCarried.hidden produce) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.supportScan produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd OuterCarried.hidden startSupport :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyCopy _ _ (by decide) (by decide),
      assemblyCopy _ _ (by decide) (by decide)⟩
  have hfinish : AvoidsCmd OuterCarried.hidden finishSupport :=
    ⟨assemblyCopy _ _ (by decide) (by decide),assemblyTransfer _ _ (by decide) (by decide),projection,
      assemblyMove _ _ (by decide) (by decide),assemblyMove _ _ (by decide) (by decide),normalization,
      assemblyMove _ _ (by decide) (by decide),assemblyClear _ (by decide),assemblyClear _ (by decide)⟩
  exact ⟨hstart,headScan produce hp,hfinish⟩

theorem command (produce : Code) (hp : AvoidsCmd OuterCarried.hidden produce) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.command produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd OuterCarried.hidden startBucket :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide),
      assemblyTake _ _ _ (by decide) (by decide),assemblyCopy _ _ (by decide) (by decide)⟩
  exact ⟨hstart,supportScan produce hp,assemblyClear _ (by decide),assemblyClear _ (by decide)⟩

theorem denseCommand (produce : Code) (hp : AvoidsCmd OuterCarried.hidden produce) :
    AvoidsCmd OuterCarried.hidden (MomentsAssembly.denseCommand produce) := ⟨command produce hp,readout⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape

end OAI.Algorithms
