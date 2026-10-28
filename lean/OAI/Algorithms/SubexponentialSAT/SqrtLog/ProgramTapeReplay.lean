import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Exact-time replay under replacement of syntactically untouched tapes. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls

variable {r s l : ℕ}

def rebaseStacks (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) : Fin s → List Bool :=
  fun i => if H i then frame i else data i

def rebaseState (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) : StructuredProgram.State r s :=
  ⟨a.regs, rebaseStacks H frame a.stacks⟩

def rebaseCfg (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : Cfg r s l) : Cfg r s l :=
  ⟨a.pc, a.regs, rebaseStacks H frame a.stacks⟩

@[simp] theorem rebaseStacks_of_mem (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (hi : H i) :
    rebaseStacks H frame data i = frame i := ite_eq_left hi

@[simp] theorem rebaseStacks_of_not_mem (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (hi : ¬ H i) :
    rebaseStacks H frame data i = data i := ite_eq_right hi

@[simp] theorem rebaseState_regs (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) :
    (rebaseState H frame a).regs = a.regs := rfl

@[simp] theorem rebaseCfg_withPC (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.State r s) (pc : Option (Fin l)) :
    rebaseCfg H frame (a.withPC pc) = (rebaseState H frame a).withPC pc := rfl

@[simp] theorem rebaseStacks_update (H : Fin s → Prop) [DecidablePred H]
    (frame data : Fin s → List Bool) (i : Fin s) (value : List Bool) (hi : ¬ H i) :
    rebaseStacks H frame (Function.update data i value) =
      Function.update (rebaseStacks H frame data) i value := by
  funext j
  by_cases hj : j = i
  · subst j; simp [rebaseStacks,hi]
  · simp [rebaseStacks,Function.update_of_ne hj]

/-- Even a peek is excluded: this is a no-read and no-write condition. -/
abbrev AvoidsInstr (H : Fin s → Prop) : Instr r s l → Prop
  | .push i _ _ => ¬ H i
  | .peek i _ _ _ => ¬ H i
  | .pop i _ _ _ => ¬ H i
  | _ => True

abbrev AvoidsProgram (H : Fin s → Prop) (p : Program r s l) : Prop :=
  ∀ q, AvoidsInstr H (p.code q)

theorem execInstr_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (i : Instr r s l) (a : Cfg r s l)
    (hi : AvoidsInstr H i) :
    execInstr i (rebaseCfg H frame a) = rebaseCfg H frame (execInstr i a) := by
  cases i <;> simp only [AvoidsInstr] at hi <;>
    (simp [execInstr,rebaseCfg,hi,rebaseStacks_update] <;> rfl)

theorem step_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (p : Program r s l) (hp : AvoidsProgram H p)
    (a : Cfg r s l) :
    step p (rebaseCfg H frame a) = (step p a).map (rebaseCfg H frame) := by
  cases hpc : a.pc with
  | none => simp [step,rebaseCfg,hpc]
  | some q =>
    simp only [step,rebaseCfg,hpc,Option.map_some]
    exact congrArg some (execInstr_rebase H frame (p.code q) a (hp q))

theorem trace_rebase (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p) {n : ℕ} {a b : Cfg r s l}
    (h : Trace p n a b) (frame : Fin s → List Bool) :
    Trace p n (rebaseCfg H frame a) (rebaseCfg H frame b) := by
  induction h with
  | refl a => exact .refl _
  | @cons n a b c hab hbc ih =>
    exact .cons (by rw [step_rebase H frame p hp,hab]; rfl) ih

theorem runsIn_rebase (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p) {n : ℕ} {a b : Cfg r s l}
    (h : RunsIn p n a b) (frame : Fin s → List Bool) :
    RunsIn p n (rebaseCfg H frame a) (rebaseCfg H frame b) := by
  obtain ⟨k,hk,ht⟩ := h
  exact ⟨k,hk,trace_rebase H hp ht frame⟩

abbrev AvoidsAtom (H : Fin s → Prop) : StructuredProgram.Atom r s → Prop
  | .push i _ => ¬ H i
  | .peek i _ _ => ¬ H i
  | .pop i _ _ => ¬ H i
  | _ => True

abbrev AvoidsBase (H : Fin s → Prop) : StructuredProgram.Cmd r s → Prop
  | .skip => True
  | .atom a => AvoidsAtom H a
  | .seq a b => AvoidsBase H a ∧ AvoidsBase H b
  | .ite _ a b => AvoidsBase H a ∧ AvoidsBase H b
  | .while _ a => AvoidsBase H a

abbrev AvoidsCmd (H : Fin s → Prop) : StructuredCalls.Cmd r s → Prop
  | .base a => AvoidsBase H a
  | .call p => AvoidsProgram H p
  | .seq a b => AvoidsCmd H a ∧ AvoidsCmd H b
  | .ite _ a b => AvoidsCmd H a ∧ AvoidsCmd H b
  | .while _ a => AvoidsCmd H a

theorem atom_instr_avoids (H : Fin s → Prop) (a : StructuredProgram.Atom r s)
    (ha : AvoidsAtom H a) (next : Fin l) : AvoidsInstr H (a.instr next) := by
  cases a <;> exact ha

theorem atom_eval_rebase (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : StructuredProgram.Atom r s)
    (ha : AvoidsAtom H a) (d : StructuredProgram.State r s) :
    a.eval (rebaseState H frame d) = rebaseState H frame (a.eval d) :=
  congrArg StructuredProgram.State.ofCfg
    (execInstr_rebase H frame (a.instr (0 : Fin 1)) (d.withPC none)
      (atom_instr_avoids H a ha _))

theorem base_eval_rebase (H : Fin s → Prop) [DecidablePred H]
    {c : StructuredProgram.Cmd r s} (hc : AvoidsBase H c)
    {n : ℕ} {a b : StructuredProgram.State r s} (h : StructuredProgram.Eval c n a b)
    (frame : Fin s → List Bool) :
    StructuredProgram.Eval c n (rebaseState H frame a) (rebaseState H frame b) := by
  induction h with
  | skip d => exact .skip _
  | atom op d =>
    rw [← atom_eval_rebase H frame op hc d]
    exact .atom _ _
  | seq h₁ h₂ ih₁ ih₂ => exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | ite_true ht he ih => exact .ite_true ht (ih hc.1)
  | ite_false ht he ih => exact .ite_false ht (ih hc.2)
  | while_false ht => exact .while_false ht
  | while_true ht hb hw ihb ihw => exact .while_true ht (ihb hc) (ihw hc)

/-- Same finite execution length, same registers, and the same visible output tapes. -/
theorem eval_rebase (H : Fin s → Prop) [DecidablePred H]
    {c : StructuredCalls.Cmd r s} (hc : AvoidsCmd H c)
    {n : ℕ} {a b : StructuredProgram.State r s} (h : StructuredCalls.Eval c n a b)
    (frame : Fin s → List Bool) :
    StructuredCalls.Eval c n (rebaseState H frame a) (rebaseState H frame b) := by
  induction h with
  | base he => exact .base (base_eval_rebase H hc he frame)
  | call p ht => exact .call p (trace_rebase H hc ht frame)
  | seq h₁ h₂ ih₁ ih₂ => exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | ite_true ht he ih => exact .ite_true ht (ih hc.1)
  | ite_false ht he ih => exact .ite_false ht (ih hc.2)
  | while_false ht => exact .while_false ht
  | while_true ht hb hw ihb ihw => exact .while_true ht (ihb hc) (ihw hc)

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
