import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Inverse projection and exact frame recovery for actual lifted programs.
The program labels are unchanged by port lifting. No execution is added or
postulated: every projected step comes from the concrete lifted instruction. -/

namespace SubexponentialSAT.ProgramProjection

open BitProgram ProgramLinking StructuredCalls

def projectCfg {r s R S l : ℕ} (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (c : Cfg R S l) : Cfg r s l :=
  ⟨c.pc, c.regs ∘ register, c.stacks ∘ stack⟩

private theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hp; cases hr; cases hs; rfl

theorem embedCfg_project {r s R S l : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (a : Cfg R S l)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    embedCfg register stack id none a (projectCfg register stack a) = a := by
  apply embedCfg_eq_of_ports register stack id none a a _ hr hs
  · cases h : a.pc <;> simp [projectCfg, relocatePc, h]
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

theorem projectCfg_embed {r s R S l : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l) (a : Cfg r s l)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    projectCfg register stack (embedCfg register stack id none frame a) = a := by
  apply cfg_ext
  · cases h : a.pc <;> simp [projectCfg, embedCfg, relocatePc, h]
  · funext i
    exact embedCfg_register register stack id none frame a hr i
  · funext i
    exact embedCfg_stack register stack id none frame a hs i

theorem project_execInstr {r s R S l : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (instr : Instr r s l) (a : Cfg R S l) :
    projectCfg register stack (execInstr (relocateInstr register stack id none instr) a) =
      execInstr instr (projectCfg register stack a) := by
  have h := execInstr_relocate register stack id none a hr hs instr (projectCfg register stack a)
  rw [embedCfg_project register stack a hr hs] at h
  have hp := congrArg (projectCfg register stack) h
  simpa only [projectCfg_embed register stack a _ hr hs] using hp

theorem project_step {r s R S l : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : Cfg R S l) :
    step p (projectCfg register stack a) =
      (step (liftProgram p register stack) a).map (projectCfg register stack) := by
  cases hp : a.pc with
  | none => simp [step, projectCfg, hp]
  | some pc =>
      simp only [step, projectCfg, hp, Option.map_some]
      change some (execInstr (p.code pc) (projectCfg register stack a)) =
        some (projectCfg register stack
          (execInstr (relocateInstr register stack id none (p.code pc)) a))
      rw [project_execInstr register stack hr hs]

theorem project_liftProgram_trace {r s R S l n : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {a b : Cfg R S l} (h : Trace (liftProgram p register stack) n a b) :
    Trace p n (projectCfg register stack a) (projectCfg register stack b) := by
  induction h with
  | refl a => exact .refl _
  | cons hstep htail ih =>
      apply Computation.Trace.cons _ ih
      rw [project_step p register stack hr hs, hstep]
      rfl

/-- Lifting preserves every unassigned cell throughout an actual execution. -/
theorem liftProgram_trace_frame {r s R S l n : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {a b : Cfg R S l} (h : Trace (liftProgram p register stack) n a b) :
    b = embedCfg register stack id none a (projectCfg register stack b) := by
  have hp := project_liftProgram_trace p register stack hr hs h
  have hl := liftProgram_trace p register stack a hr hs hp
  rw [embedCfg_project register stack a hr hs] at hl
  exact Option.some.inj (h.iterate.symm.trans hl.iterate)

theorem relocateInstr_comp {r s R S T U l : ℕ}
    (reg₁ : Fin r → Fin R) (stk₁ : Fin s → Fin S)
    (reg₂ : Fin R → Fin T) (stk₂ : Fin S → Fin U) (instr : Instr r s l) :
    relocateInstr reg₂ stk₂ id none (relocateInstr reg₁ stk₁ id none instr) =
      relocateInstr (reg₂ ∘ reg₁) (stk₂ ∘ stk₁) id none instr := by
  cases instr <;> rfl

theorem liftProgram_comp {r s R S T U l : ℕ} (p : Program r s l)
    (reg₁ : Fin r → Fin R) (stk₁ : Fin s → Fin S)
    (reg₂ : Fin R → Fin T) (stk₂ : Fin S → Fin U) :
    liftProgram (liftProgram p reg₁ stk₁) reg₂ stk₂ =
      liftProgram p (reg₂ ∘ reg₁) (stk₂ ∘ stk₁) := by
  cases p
  simp only [liftProgram]
  congr 1
  funext pc
  exact relocateInstr_comp reg₁ stk₁ reg₂ stk₂ _

theorem project_call {r s R S l n : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {a b : State R S} (h : Eval (.call (liftProgram p register stack)) n a b) :
    Eval (.call p) n (projectState register stack a) (projectState register stack b) := by
  cases h with
  | call _ h =>
      apply Eval.call
      exact project_liftProgram_trace p register stack hr hs h

theorem call_frame {r s R S l n : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {a b : State R S} (h : Eval (.call (liftProgram p register stack)) n a b) :
    b = embedState register stack a (projectState register stack b) := by
  cases h with
  | call _ h =>
      exact congrArg StructuredProgram.State.ofCfg
        (liftProgram_trace_frame p register stack hr hs h)

end SubexponentialSAT.ProgramProjection

end OAI.Algorithms
