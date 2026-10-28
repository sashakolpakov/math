import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r s l : ℕ}

theorem clear (src : Fin 768) (v p : Fin r) (h : ¬collectorTape src) :
    AvoidsCmd collectorTape (.call (StackRoutines.clearProgram src v p)) :=
  avoids_clearProgram collectorTape src v p h

theorem transfer (src dst : Fin 768) (v p : Fin r)
    (hs : ¬collectorTape src) (hd : ¬collectorTape dst) :
    AvoidsCmd collectorTape (.call (StackRoutines.transferProgram src dst v p)) :=
  avoids_transferProgram collectorTape src dst v p hs hd

theorem copy (src dst tmp : Fin 768) (v p : Fin r)
    (hs : ¬collectorTape src) (hd : ¬collectorTape dst) (ht : ¬collectorTape tmp) :
    AvoidsCmd collectorTape (.call (StackRoutines.copyProgram src dst tmp v p)) :=
  avoids_copyProgram collectorTape src dst tmp v p hs hd ht

theorem reverse (src dst tmp : Fin 768) (v p : Fin r)
    (hs : ¬collectorTape src) (hd : ¬collectorTape dst) (ht : ¬collectorTape tmp) :
    AvoidsCmd collectorTape (.call (StackRoutines.reverseProgram src dst tmp v p)) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd,ht]

theorem liftProgram (program : Program r s l) (register : Fin r → Fin 40)
    (stack : Fin s → Fin 768) (hs : ∀ i,¬collectorTape (stack i)) :
    AvoidsCmd collectorTape (.call (ProgramLinking.liftProgram program register stack)) :=
  avoids_call_lift_of_range collectorTape program register stack hs

theorem liftCommand (command : Cmd r s) (input output : Fin s)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 768)
    (hs : ∀ i,¬collectorTape (stack i)) :
    AvoidsCmd collectorTape (StructuredCalls.liftCommand command input output register stack) :=
  liftProgram _ _ _ hs

theorem reader (ports : RecordPrograms.Ports r 768)
    (hs : ¬collectorTape ports.source) (hd : ¬collectorTape ports.payload) :
    AvoidsCmd collectorTape (RecordPrograms.reader ports) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> simpa [RecordPrograms.stackMap] using (by first | exact hs | exact hd)

theorem records (ports : RecordPrograms.Ports r 768) (callback : Cmd r 768)
    (hs : ¬collectorTape ports.source) (hd : ¬collectorTape ports.payload)
    (hc : AvoidsCmd collectorTape callback) :
    AvoidsCmd collectorTape (RecordPrograms.iterate ports callback) := by
  have hr := reader ports hs hd
  simp only [
    AvoidsCmd,AvoidsBase,AvoidsAtom]
  exact ⟨trivial,hs,hr,hc,trivial,hs⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.Tape

end OAI.Algorithms
