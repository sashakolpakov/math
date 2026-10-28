import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_liftCommand_of_range {R S : ℕ} (H : Fin S → Prop)
    (c : Cmd r s) (input output : Fin s) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (liftCommand c input output register stack) :=
  avoids_call_lift_of_range H _ register stack h

theorem avoids_copyCmd (H : Fin s → Prop) (src dst tmp : Fin s)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsCmd H (SubexpSetupStorage.copyCmd src dst tmp) :=
  avoids_copyProgram H src dst tmp 0 1 hs hd ht

theorem avoids_clearCmd (H : Fin s → Prop) (src : Fin s) (hs : ¬ H src) :
    AvoidsCmd H (SubexpSetupStorage.clearCmd src) :=
  avoids_clearProgram H src 0 1 hs

theorem avoids_copyMany (H : Fin s → Prop) (tmp : Fin s)
    (ps : List (Fin s × Fin s)) (ht : ¬ H tmp)
    (hp : ∀ p ∈ ps, ¬ H p.1 ∧ ¬ H p.2) :
    AvoidsCmd H (SubexpSetupStorage.copyMany tmp ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_copyCmd H p.1 p.2 tmp (hp p (by simp)).1 (hp p (by simp)).2 ht,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem avoids_clearMany (H : Fin s → Prop) (ps : List (Fin s))
    (hp : ∀ p ∈ ps, ¬ H p) : AvoidsCmd H (SubexpSetupStorage.clearMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨avoids_clearCmd H p (hp p (by simp)), ih (fun q hq => hp q (by simp [hq]))⟩

theorem avoids_resetMany (H : Fin s → Prop) (ps : List (Fin 16)) :
    AvoidsCmd H (SubexpSetupStorage.resetMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

theorem avoids_forCmd (H : Fin s → Prop) (p : UnaryForPrograms.Ports r s)
    (body : Cmd r s) (hp : ¬ H p.counter) (hb : AvoidsCmd H body) :
    AvoidsCmd H (UnaryForPrograms.forCmd p body) := ⟨hp,hb,hp⟩

theorem avoids_pushConst (H : Fin s → Prop) (dst : Fin s) (reg : Fin r) (b : Bool)
    (hd : ¬ H dst) : AvoidsCmd H (Subexp.TupleProgram.pushConst dst reg b) := ⟨trivial,hd⟩

theorem avoids_record_reader (H : Fin s → Prop) (p : RecordPrograms.Ports r s)
    (hs : ¬ H p.source) (hp : ¬ H p.payload) : AvoidsCmd H (RecordPrograms.reader p) := by
  apply avoids_call_lift_of_range
  intro i
  unfold RecordPrograms.stackMap
  split <;> assumption

theorem avoids_record_iterate (H : Fin s → Prop) (p : RecordPrograms.Ports r s)
    (body : Cmd r s) (hs : ¬ H p.source) (hp : ¬ H p.payload)
    (hb : AvoidsCmd H body) : AvoidsCmd H (RecordPrograms.iterate p body) :=
  ⟨trivial,hs,avoids_record_reader H p hs hp,hb,trivial,hs⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
