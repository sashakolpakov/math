import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r s l : ℕ}

theorem clear (src : Fin 768) (v p : Fin r) (h : ¬OuterCarried.hidden src) :
    AvoidsCmd OuterCarried.hidden (.call (StackRoutines.clearProgram src v p)) :=
  avoids_clearProgram OuterCarried.hidden src v p h

theorem transfer (src dst : Fin 768) (v p : Fin r)
    (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) :
    AvoidsCmd OuterCarried.hidden (.call (StackRoutines.transferProgram src dst v p)) :=
  avoids_transferProgram OuterCarried.hidden src dst v p hs hd

theorem copy (src dst tmp : Fin 768) (v p : Fin r)
    (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) (ht : ¬OuterCarried.hidden tmp) :
    AvoidsCmd OuterCarried.hidden (.call (StackRoutines.copyProgram src dst tmp v p)) :=
  avoids_copyProgram OuterCarried.hidden src dst tmp v p hs hd ht

theorem reverse (src dst tmp : Fin 768) (v p : Fin r)
    (hs : ¬OuterCarried.hidden src) (hd : ¬OuterCarried.hidden dst) (ht : ¬OuterCarried.hidden tmp) :
    AvoidsCmd OuterCarried.hidden (.call (StackRoutines.reverseProgram src dst tmp v p)) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd,ht]

theorem liftProgram (program : Program r s l) (register : Fin r → Fin 40)
    (stack : Fin s → Fin 768) (hs : ∀ i,¬OuterCarried.hidden (stack i)) :
    AvoidsCmd OuterCarried.hidden (.call (ProgramLinking.liftProgram program register stack)) :=
  avoids_call_lift_of_range OuterCarried.hidden program register stack hs

theorem liftCommand (command : Cmd r s) (input output : Fin s)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 768)
    (hs : ∀ i,¬OuterCarried.hidden (stack i)) :
    AvoidsCmd OuterCarried.hidden (StructuredCalls.liftCommand command input output register stack) :=
  liftProgram _ _ _ hs

theorem reader (ports : RecordPrograms.Ports r 768)
    (hs : ¬OuterCarried.hidden ports.source) (hd : ¬OuterCarried.hidden ports.payload) :
    AvoidsCmd OuterCarried.hidden (RecordPrograms.reader ports) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> simpa [RecordPrograms.stackMap] using (by first | exact hs | exact hd)

theorem records (ports : RecordPrograms.Ports r 768) (callback : Cmd r 768)
    (hs : ¬OuterCarried.hidden ports.source) (hd : ¬OuterCarried.hidden ports.payload)
    (hc : AvoidsCmd OuterCarried.hidden callback) :
    AvoidsCmd OuterCarried.hidden (RecordPrograms.iterate ports callback) := by
  have hr := reader ports hs hd
  simp only [
    AvoidsCmd,AvoidsBase,AvoidsAtom]
  exact ⟨trivial,hs,hr,hc,trivial,hs⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop.OuterTape

end OAI.Algorithms
