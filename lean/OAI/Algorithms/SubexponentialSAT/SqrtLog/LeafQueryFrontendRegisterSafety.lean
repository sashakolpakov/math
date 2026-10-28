import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun

namespace OAI.Algorithms

/-! Structural register frames for the actual frontend syntax. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety
open SubexponentialSAT BitProgram StructuredCalls

abbrev baseSafe {r s : ℕ} (j : Fin r) : StructuredProgram.Cmd r s → Prop
  | .skip => True
  | .atom a => ∀ d, (a.eval d).regs j=d.regs j
  | .seq a b => baseSafe j a ∧ baseSafe j b
  | .ite _ a b => baseSafe j a ∧ baseSafe j b
  | .while _ a => baseSafe j a

abbrev safe {r s : ℕ} (j : Fin r) : Cmd r s → Prop
  | .base c => baseSafe j c
  | .call p => ∀ q d, (execInstr (p.code q) d).regs j=d.regs j
  | .seq a b => safe j a ∧ safe j b
  | .ite _ a b => safe j a ∧ safe j b
  | .while _ a => safe j a

theorem base_frame {r s : ℕ} {c : StructuredProgram.Cmd r s} {n : ℕ}
    {a b : State r s} (he : StructuredProgram.Eval c n a b) (j : Fin r)
    (hs : baseSafe j c) : b.regs j=a.regs j := by
  induction he with
  | skip => rfl
  | atom a d => exact hs d
  | seq _ _ ih ih' => exact (ih' hs.2).trans (ih hs.1)
  | ite_true _ _ ih => exact ih hs.1
  | ite_false _ _ ih => exact ih hs.2
  | while_false => rfl
  | while_true _ _ _ ih ih' => exact (ih' hs).trans (ih hs)

theorem trace_frame {r s l : ℕ} (p : Program r s l) (j : Fin r)
    (hs : ∀ q d, (execInstr (p.code q) d).regs j=d.regs j)
    {n : ℕ} {a b : Cfg r s l} (he : Trace p n a b) : b.regs j=a.regs j := by
  induction he with
  | refl => rfl
  | @cons n a b c hab hbc ih =>
    apply ih.trans
    cases hp : a.pc with
    | none => simp [step,hp] at hab
    | some q =>
      have hb : execInstr (p.code q) a=b := by simpa [step,hp] using hab
      exact hb ▸ hs q a

theorem frame {r s : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (he : Eval c n a b) (j : Fin r) (hs : safe j c) : b.regs j=a.regs j := by
  induction he with
  | base he => exact base_frame he j hs
  | call p he => exact trace_frame p j hs he
  | seq _ _ ih ih' => exact (ih' hs.2).trans (ih hs.1)
  | ite_true _ _ ih => exact ih hs.1
  | ite_false _ _ ih => exact ih hs.2
  | while_false => rfl
  | while_true _ _ _ ih ih' => exact (ih' hs).trans (ih hs)

theorem lift_safe {r s l R S : ℕ} (p : Program r s l)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (j : Fin R)
    (hj : ∀ i, j≠reg i) : safe j (.call (ProgramLinking.liftProgram p reg stk)) := by
  intro q d
  dsimp [ProgramLinking.liftProgram]
  cases p.code q <;>
    simp [ProgramLinking.relocateInstr,execInstr,readRegs,hj]

theorem liftCommand_safe {r s R S : ℕ} (c : Cmd r s) (input output : Fin s)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (j : Fin R)
    (hj : ∀ i, j≠reg i) : safe j (liftCommand c input output reg stk) :=
  lift_safe _ _ _ _ hj

theorem copy_safe {r s : ℕ} (src dst tmp : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) : safe j (.call (StackRoutines.copyProgram src dst tmp v p)) := by
  intro q d
  fin_cases q <;> simp [execInstr,readRegs,hv,hp]

theorem clear_safe {r s : ℕ} (src : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) : safe j (.call (StackRoutines.clearProgram src v p)) := by
  intro q d
  fin_cases q <;> simp [execInstr,readRegs,hv,hp]

theorem clearCmd_safe {r s : ℕ} (tmp : Fin s) (v p j : Fin r)
    (hv : j≠v) (hp : j≠p) (xs : List (Fin s)) : safe j (BankRoutines.clearCmd tmp v p xs) := by
  induction xs with
  | nil => exact clear_safe _ _ _ _ hv hp
  | cons x xs ih => exact ⟨clear_safe _ _ _ _ hv hp,ih⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety

end OAI.Algorithms
