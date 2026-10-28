import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopTapeBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReadout

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem assemblyClear (src : Fin 768) (hs : ¬collectorTape src) :
    AvoidsCmd collectorTape (MomentsAssembly.clear src) := clear src 0 1 hs

theorem assemblyCopy (src dst : Fin 768) (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (MomentsAssembly.copy src dst) := copy src dst 179 0 1 hs hd (by decide)

theorem assemblyTransfer (src dst : Fin 768) (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (MomentsAssembly.transfer src dst) := transfer src dst 0 1 hs hd

theorem assemblyTake (src dst : Fin 768) (hne : src≠164)
    (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (takeFrame src dst hne) :=
  ⟨reader _ hs (by change ¬collectorTape 164; decide),assemblyTransfer 164 dst (by decide) hd⟩

theorem assemblyMove (src dst : Fin 768) (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (moveForward src dst) :=
  ⟨assemblyTransfer src 164 hs (by decide),assemblyTransfer 164 dst (by decide) hd⟩

theorem assemblyScan (src : Fin 768) (body : Code)
    (hs : ¬collectorTape src) (hb : AvoidsCmd collectorTape body) :
    AvoidsCmd collectorTape (rawScan src body) := ⟨hs,hb,hs⟩

theorem weighted : AvoidsCmd collectorTape weightedAdd :=
  liftCommand _ _ _ _ _ (by decide)

theorem product : AvoidsCmd collectorTape multiply :=
  liftProgram _ _ _ (by decide)

theorem normalization : AvoidsCmd collectorTape normalize :=
  liftCommand _ _ _ _ _ (by decide)

theorem projection : AvoidsCmd collectorTape project :=
  liftCommand _ _ _ _ _ (by decide)

theorem readout : AvoidsCmd collectorTape MomentsAssembly.readout :=
  liftProgram _ _ _ (by decide)

theorem assignmentScan (produce : Code) (hp : AvoidsCmd collectorTape produce) :
    AvoidsCmd collectorTape (MomentsAssembly.assignmentScan produce) := by
  apply assemblyScan _ _ (by decide)
  exact ⟨assemblyTake _ _ _ (by decide) (by decide),hp,weighted,assemblyClear _ (by decide)⟩

theorem headScan (produce : Code) (hp : AvoidsCmd collectorTape produce) :
    AvoidsCmd collectorTape (MomentsAssembly.headScan produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd collectorTape startHead :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide),
      assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide)⟩
  have hfinish : AvoidsCmd collectorTape finishHead :=
    ⟨assemblyMove _ _ (by decide) (by decide),product,assemblyMove _ _ (by decide) (by decide),
      assemblyClear _ (by decide),assemblyClear _ (by decide),assemblyClear _ (by decide)⟩
  exact ⟨hstart,assignmentScan produce hp,hfinish⟩

theorem supportScan (produce : Code) (hp : AvoidsCmd collectorTape produce) :
    AvoidsCmd collectorTape (MomentsAssembly.supportScan produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd collectorTape startSupport :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyCopy _ _ (by decide) (by decide),
      assemblyCopy _ _ (by decide) (by decide)⟩
  have hfinish : AvoidsCmd collectorTape finishSupport :=
    ⟨assemblyCopy _ _ (by decide) (by decide),assemblyTransfer _ _ (by decide) (by decide),projection,
      assemblyMove _ _ (by decide) (by decide),assemblyMove _ _ (by decide) (by decide),normalization,
      assemblyMove _ _ (by decide) (by decide),assemblyClear _ (by decide),assemblyClear _ (by decide)⟩
  exact ⟨hstart,headScan produce hp,hfinish⟩

theorem command (produce : Code) (hp : AvoidsCmd collectorTape produce) :
    AvoidsCmd collectorTape (MomentsAssembly.command produce) := by
  apply assemblyScan _ _ (by decide)
  have hstart : AvoidsCmd collectorTape startBucket :=
    ⟨assemblyTake _ _ _ (by decide) (by decide),assemblyTake _ _ _ (by decide) (by decide),
      assemblyTake _ _ _ (by decide) (by decide),assemblyCopy _ _ (by decide) (by decide)⟩
  exact ⟨hstart,supportScan produce hp,assemblyClear _ (by decide),assemblyClear _ (by decide)⟩

theorem denseCommand (produce : Code) (hp : AvoidsCmd collectorTape produce) :
    AvoidsCmd collectorTape (MomentsAssembly.denseCommand produce) := ⟨command produce hp,readout⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape

end OAI.Algorithms
