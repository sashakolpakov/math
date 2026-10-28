import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoidsInstr_of_all (H : Fin s → Prop) (h : ∀ i, ¬ H i) (op : Instr r s l) :
    AvoidsInstr H op := by
  cases op <;> simp_all [AvoidsInstr]

theorem avoids_relocate (H : Fin S → Prop) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (label : Fin l → Fin L) (ret : Option (Fin L))
    (op : Instr r s l) (h : AvoidsInstr (H ∘ stack) op) :
    AvoidsInstr H (ProgramLinking.relocateInstr register stack label ret op) := by
  cases op <;> cases ret <;> exact h

theorem avoids_liftProgram (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (h : AvoidsProgram (H ∘ stack) p) :
    AvoidsProgram H (ProgramLinking.liftProgram p register stack) := by
  intro q
  exact avoids_relocate H register stack id none (p.code q) (h q)

/-- No inspection of the local program is necessary when every mapped tape is visible. -/
theorem avoids_liftProgram_of_range (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (h : ∀ i, ¬ H (stack i)) :
    AvoidsProgram H (ProgramLinking.liftProgram p register stack) :=
  avoids_liftProgram H p register stack (fun q => avoidsInstr_of_all (H ∘ stack) h (p.code q))

theorem avoids_call_lift_of_range (H : Fin S → Prop) (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (.call (ProgramLinking.liftProgram p register stack)) :=
  avoids_liftProgram_of_range H p register stack h

theorem avoids_base_code (H : Fin s → Prop) (c : StructuredProgram.Cmd r s)
    (hc : AvoidsBase H c) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    AvoidsInstr H (StructuredProgram.code c embed exit q) := by
  induction c generalizing exit with
  | skip => exact q.elim
  | atom a => exact atom_instr_avoids H a hc exit
  | seq first second ih₁ ih₂ =>
    cases q with
    | inl q => exact ih₁ hc.1 _ _ q
    | inr q => exact ih₂ hc.2 _ _ q
  | ite test yes no ih₁ ih₂ =>
    cases q with
    | none => trivial
    | some q =>
      cases q with
      | inl q => exact ih₁ hc.1 _ _ q
      | inr q => exact ih₂ hc.2 _ _ q
  | «while» test body ih =>
    cases q with
    | none => trivial
    | some q => exact ih hc _ _ q

theorem avoids_base_compiled (H : Fin s → Prop) (c : StructuredProgram.Cmd r s)
    (hc : AvoidsBase H c) (input output : Fin s) :
    AvoidsProgram H (StructuredProgram.compiled c input output) := by
  intro q
  simp only [StructuredProgram.compiled]
  split
  · trivial
  · exact avoids_base_code H c hc _ _ _

theorem avoids_code (H : Fin s → Prop) (c : StructuredCalls.Cmd r s)
    (hc : AvoidsCmd H c) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    AvoidsInstr H (StructuredCalls.code c embed exit q) := by
  induction c generalizing exit with
  | base c => exact avoids_base_code H c hc embed exit q
  | call p => exact avoids_relocate H id id embed (some exit) (p.code q) (hc q)
  | seq first second ih₁ ih₂ =>
    cases q with
    | inl q => exact ih₁ hc.1 _ _ q
    | inr q => exact ih₂ hc.2 _ _ q
  | ite test yes no ih₁ ih₂ =>
    cases q with
    | none => trivial
    | some q =>
      cases q with
      | inl q => exact ih₁ hc.1 _ _ q
      | inr q => exact ih₂ hc.2 _ _ q
  | «while» test body ih =>
    cases q with
    | none => trivial
    | some q => exact ih hc _ _ q

theorem avoids_compiled (H : Fin s → Prop) (c : StructuredCalls.Cmd r s)
    (hc : AvoidsCmd H c) (input output : Fin s) :
    AvoidsProgram H (StructuredCalls.compiled c input output) := by
  intro q
  simp only [StructuredCalls.compiled]
  split
  · trivial
  · exact avoids_code H c hc _ _ _

theorem avoids_clearProgram (H : Fin s → Prop) (src : Fin s) (value present : Fin r)
    (hs : ¬ H src) : AvoidsProgram H (StackRoutines.clearProgram src value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs]

theorem avoids_transferProgram (H : Fin s → Prop) (src dst : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsProgram H (StackRoutines.transferProgram src dst value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd]

theorem avoids_copyProgram (H : Fin s → Prop) (src dst tmp : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) (ht : ¬ H tmp) :
    AvoidsProgram H (StackRoutines.copyProgram src dst tmp value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd,ht]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
