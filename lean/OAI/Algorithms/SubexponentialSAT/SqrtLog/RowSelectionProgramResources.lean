import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! Stack-size accounting and fixed cleanup loops for signed minor arithmetic. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem instr_stack_length {r s l : ℕ} (i : Instr r s l)
    (a : Cfg r s l) (j : Fin s) :
    ((execInstr i a).stacks j).length ≤ (a.stacks j).length + 1 := by
  cases i <;> simp only [execInstr]
  all_goals try omega
  case push stack src next =>
    by_cases h : j = stack
    · subst j; simp
    · simp [h]
  case pop stack value present next =>
    by_cases h : j = stack
    · subst j; simp; omega
    · simp [h]

theorem trace_stack_length {r s l : ℕ} (p : Program r s l) {t : ℕ}
    {a b : Cfg r s l} (h : Trace p t a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + t := by
  induction h with
  | refl => omega
  | @cons t a b c hs ht ih =>
    have hb : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
      cases hp : a.pc with
      | none => simp [step, hp] at hs
      | some q =>
        have he : execInstr (p.code q) a = b := by simpa [step, hp] using hs
        rw [← he]
        exact instr_stack_length _ _ _
    omega

theorem eval_stack_length {r s : ℕ} {c : Cmd r s} {t : ℕ}
    {a b : State r s} (h : Eval c t a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + t := by
  exact trace_stack_length _ (compiled_trace h j j) j

abbrev clearAt (j : Fin 15) : Cmd 8 15 :=
  .call (StackRoutines.clearProgram j 0 1)

def clearedAt (j : Fin 15) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩

theorem clearAt_eval (j : Fin 15) (d : Data) :
    Eval (clearAt j) (2*(d.stacks j).length+3) d (clearedAt j d) := by
  simpa only [clearAt, clearedAt, StackRoutines.clearStacks] using
    Subexp.TupleProgram.clear_eval j 0 1 d

def clearList : List (Fin 15) → Cmd 8 15
  | [] => .base .skip
  | j :: js => .seq (clearAt j) (clearList js)

def clearedList : List (Fin 15) → Data → Data
  | [], d => d
  | j :: js, d => clearedList js (clearedAt j d)

@[simp] theorem clearedList_stack (js : List (Fin 15)) (d : Data) (j : Fin 15) :
    (clearedList js d).stacks j = if j ∈ js then [] else d.stacks j := by
  induction js generalizing d with
  | nil => simp [clearedList]
  | cons i js ih =>
    simp only [clearedList, ih, List.mem_cons, clearedAt]
    by_cases h : j = i
    · subst j; simp
    · by_cases hj : j ∈ js <;> simp_all

theorem clearList_eval (js : List (Fin 15)) (d : Data) :
    ∃ t ≤ (js.map fun j => 2*(d.stacks j).length+3).sum,
      Eval (clearList js) t d (clearedList js d) := by
  induction js generalizing d with
  | nil => exact ⟨0, by simp, .base (.skip _)⟩
  | cons j js ih =>
    obtain ⟨t, ht, he⟩ := ih (clearedAt j d)
    refine ⟨2*(d.stacks j).length+3+t, ?_, (clearAt_eval j d).seq he⟩
    simp only [List.map_cons, List.sum_cons]
    have hm : (js.map fun i => 2*((clearedAt j d).stacks i).length+3).sum ≤
        (js.map fun i => 2*(d.stacks i).length+3).sum := by
      apply List.sum_le_sum
      intro i hi
      by_cases hij : i = j <;> simp [clearedAt, hij]
    omega

/-- Cleanup bound expressed by a uniform bound on the input stack lengths. -/
theorem clearList_eval_bounded (js : List (Fin 15)) (d : Data) (B : ℕ)
    (hb : ∀ j ∈ js, (d.stacks j).length ≤ B) :
    ∃ t ≤ js.length*(2*B+3), Eval (clearList js) t d (clearedList js d) := by
  obtain ⟨t, ht, he⟩ := clearList_eval js d
  refine ⟨t, ht.trans ?_, he⟩
  calc
    (js.map fun j => 2*(d.stacks j).length+3).sum ≤
        (js.map fun _ => 2*B+3).sum := by
      apply List.sum_le_sum
      intro j hj
      have := hb j hj
      omega
    _ = js.length*(2*B+3) := by simp

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
