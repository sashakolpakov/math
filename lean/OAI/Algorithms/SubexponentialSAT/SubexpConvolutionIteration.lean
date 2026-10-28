import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

def testResult (counter : Fin 256) (flag : Fin 16) (d : Data) : Data :=
  (StructuredProgram.Atom.peek counter 0 flag).eval d

theorem test_eval (counter : Fin 256) (flag : Fin 16) (d : Data) :
    Eval (test counter flag) 1 d (testResult counter flag d) :=
  .base (.atom _ _)

@[simp] theorem testResult_stacks (counter : Fin 256) (flag : Fin 16) (d : Data) :
    (testResult counter flag d).stacks = d.stacks := rfl

theorem testResult_flag (counter : Fin 256) (flag : Fin 16) (d : Data) :
    (testResult counter flag d).regs flag = decide (0 < (d.stacks counter).length) := by
  cases h : d.stacks counter with
  | nil => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]
  | cons b bs => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]

def unaryLoop (counter : Fin 256) (flag : Fin 16) (body : Code) : Code :=
  .while flag (.seq body (test counter flag))

def unaryRun (counter : Fin 256) (flag : Fin 16) (body : Code) : Code :=
  .seq (test counter flag) (unaryLoop counter flag body)

/-- One branch test per iteration plus the final failing branch. -/
def unaryBudget (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | fuel + 1 => cost (fuel + 1) + unaryBudget cost fuel + 2

theorem unaryLoop_eval (counter : Fin 256) (flag : Fin 16)
    (body : Code) (Inv : ℕ → (Fin 256 → List Bool) → Prop) (cost : ℕ → ℕ)
    (hcount : ∀ fuel stk, Inv fuel stk → (stk counter).length = fuel)
    (hstep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval body n d e ∧ n ≤ cost (fuel + 1) ∧ Inv fuel e.stacks)
    (fuel : ℕ) :
    ∀ d : Data, Inv fuel d.stacks → d.regs flag = decide (0 < fuel) →
      ∃ n e, Eval (unaryLoop counter flag body) n d e ∧
        n ≤ unaryBudget cost fuel ∧ Inv 0 e.stacks := by
  induction fuel with
  | zero =>
      intro d hd hg
      exact ⟨1, d, .while_false (by simpa using hg), by rfl, hd⟩
  | succ fuel ih =>
      intro d hd hg
      obtain ⟨nb, e, hb, hnb, he⟩ := hstep fuel d hd
      have htest := test_eval counter flag e
      have he' : Inv fuel (testResult counter flag e).stacks := he
      have hflag' : (testResult counter flag e).regs flag = decide (0 < fuel) := by
        rw [testResult_flag counter flag, hcount fuel e.stacks he]
      obtain ⟨nt, f, ht, hnt, hf⟩ := ih (testResult counter flag e) he' hflag'
      refine ⟨(nb + 1) + nt + 1, f,
        .while_true (by simpa using hg) (.seq hb htest) ht, ?_, hf⟩
      simp only [unaryBudget]
      omega

/-- The initial physical peek is included in the bound. The body may change
all registers because the next peek establishes the loop guard anew. -/
theorem unaryRun_eval (counter : Fin 256) (flag : Fin 16)
    (body : Code) (Inv : ℕ → (Fin 256 → List Bool) → Prop) (cost : ℕ → ℕ)
    (hcount : ∀ fuel stk, Inv fuel stk → (stk counter).length = fuel)
    (hstep : ∀ fuel (d : Data), Inv (fuel + 1) d.stacks →
      ∃ n e, Eval body n d e ∧ n ≤ cost (fuel + 1) ∧ Inv fuel e.stacks)
    (fuel : ℕ) (d : Data) (hd : Inv fuel d.stacks) :
    ∃ n e, Eval (unaryRun counter flag body) n d e ∧
      n ≤ 1 + unaryBudget cost fuel ∧ Inv 0 e.stacks := by
  obtain ⟨n, e, he, hn, hIe⟩ := unaryLoop_eval counter flag body Inv cost hcount hstep fuel
    (testResult counter flag d) hd (by
      rw [testResult_flag counter flag, hcount fuel d.stacks hd])
  exact ⟨1 + n, e, .seq (test_eval counter flag d) he, Nat.add_le_add_left hn 1, hIe⟩

theorem unaryBudget_le (cost : ℕ → ℕ) (C fuel : ℕ)
    (hc : ∀ i, 0 < i → i ≤ fuel → cost i ≤ C) :
    unaryBudget cost fuel ≤ fuel * (C + 2) + 1 := by
  induction fuel with
  | zero => simp [unaryBudget]
  | succ fuel ih =>
      have hprev := ih (fun i hi hif => hc i hi (by omega))
      have hcur := hc (fuel + 1) (by omega) (by omega)
      simp only [unaryBudget, Nat.succ_mul]
      omega

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
