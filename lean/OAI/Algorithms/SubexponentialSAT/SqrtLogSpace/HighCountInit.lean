import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CopySpace

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def changed : List (Fin 896) := [788,789,790,323,791,792]
def reset : Code := .seq (.call (clearProgram 792 0 1))
  (BankRoutines.clearCmd 792 0 1 changed)
def resetState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks changed a.stacks⟩
def resetCost (a : Data) := 2*(a.stacks 792).length+3+
  (2*(changed.map (fun i => ((clearStacks 792 a.stacks) i).length)).sum+21)

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (792 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 792 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (clearStacks 792 a.stacks)=
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i∈changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i≠792 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=6 from rfl,
    hs,readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem reset_blank (a : Data) (i : Fin 896) (hi : i∈changed) :
    (resetState a).stacks i=[] := BankRoutines.clearBankStacks_mem i changed a.stacks hi

def copy : Code := .call (copyProgram 330 789 792 0 1)
def copied (a : Data) : Data :=
  ⟨readRegs (resetState a).regs 0 1 none,copyStacks 330 789 (resetState a).stacks⟩
def result (a : Data) : Data := ⟨Function.update (copied a).regs 21 true,(copied a).stacks⟩
def command : Code := .seq reset (.seq copy restoreHighGuard)
def program := compiled command 330 788
def cost (a : Data) := resetCost a+7*(a.stacks 330).length+6

theorem copy_eval (a : Data) : Eval copy (7*(a.stacks 330).length+5) (resetState a) (copied a) := by
  unfold copy copied
  apply Eval.call
  simpa only [reset_frame a 330 (by decide)] using
    ListRegisterProgram.copy_run (330 : Fin 896) 789 792 (0 : Fin 40) 1
      (by decide) (by decide) (by decide) (by decide)
      (resetState a).regs (resetState a).stacks (reset_blank a 792 (by decide))

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  simpa only [command, cost, result, Nat.add_assoc] using
    (reset_eval a).seq ((copy_eval a).seq (restoreHighGuard_eval (copied a)))

@[simp] theorem counter (a : Data) : (result a).stacks 789=a.stacks 330 := by
  simp [result,copied,copyStacks,reset_frame a 330 (by decide),reset_blank a 789 (by decide)]

@[simp] theorem blank (a : Data) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) : (result a).stacks i=[] := by
  have hn : i≠789 := by intro h; subst i; simp at hi
  have hc : i∈changed := by simpa [changed,List.mem_cons,or_assoc,or_left_comm,or_comm] using
    (show i=789 ∨ i∈([788,790,323,791,792] : List (Fin 896)) from Or.inr hi)
  simp [result,copied,copyStacks,hn,reset_blank a i hc]

theorem frame (a : Data) (i : Fin 896) (hi : i∉changed) : (result a).stacks i=a.stacks i := by
  have hn : i≠789 := by intro h; subst i; exact hi (by decide)
  simp [result,copied,copyStacks,hn,reset_frame a i hi]

@[simp] theorem guard (a : Data) : (result a).regs 21=true := by simp [result]

theorem ready {I : Data → Prop} (a : Data) (hi : I (result a)) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ready highPorts I (result a) :=
  ⟨hi,blank a 323 (by decide),blank a 791 (by decide)⟩

theorem return_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((result a).stacks i).length≤bound := by
  intro i
  by_cases hc : i=789
  · subst i; rw [counter]; exact hb 330
  · by_cases hs : i∈([788,790,323,791,792] : List (Fin 896))
    · rw [blank a i hs]; exact Nat.zero_le _
    · rw [frame a i (by simpa [changed,hc] using hs)]; exact hb i

private theorem reset_bound (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ i, ((resetState a).stacks i).length≤bound := by
  intro i
  by_cases hi : i∈changed
  · rw [reset_blank a i hi]; exact Nat.zero_le _
  · rw [reset_frame a i hi]; exact hb i

private theorem reset_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q≤resetCost a → Trace (compiled reset 330 788) q
      (a.withPC (some (compiled reset 330 788).entry)) z → ∀ i, (z.stacks i).length≤bound := by
  let middle : Data := ⟨readRegs a.regs 0 1 none,clearStacks 792 a.stacks⟩
  have first := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (792 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle.regs middle.stacks (by simp [middle])
  have hfirst := HighQuerySpace.clear_bound (792 : Fin 896) (0 : Fin 40) 1 a bound hb 330 788
  have hrest := HighQuerySpace.clear_bank_bound (792 : Fin 896) (0 : Fin 40) 1 changed
    (by decide) middle (by simp [middle]) bound
    (HighQuerySpace.clear_state_bound 792 0 1 a bound hb) 330 788
  exact StructuredSpace.sequence_stack_bound first rest 330 788 hfirst hrest
    _ _ _ (compiled_site reset 330 788)

private theorem copy_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    ∀ q z, q≤7*(a.stacks 330).length+5 → Trace (compiled copy 330 788) q
      ((resetState a).withPC (some (compiled copy 330 788).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
  have he := copy_eval a
  cases he with
  | call p tr =>
    apply StructuredSpace.call_stack_bound _ _ _ _ (compiled_site copy 330 788) tr
    intro q z _ hq
    exact CopySpace.copyProgram_no_growth 330 789 792 0 1 (by decide) (by decide) (by decide)
      rfl (reset_blank a 789 (by decide)) (reset_blank a 792 (by decide)) (reset_bound a bound hb) hq

/-- Every prefix retains the same caller envelope; both cleanup and copy are
proved without a time-based amplification of all retained caller stacks. -/
theorem trace_space (a : Data) (bound : ℕ) (hb : ∀ i, (a.stacks i).length≤bound) :
    Trace program (cost a+1) (a.withPC (some program.entry)) ((result a).withPC none) ∧
      cost a+1≤21*bound+31 ∧
      ∀ q z, q≤cost a+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length≤bound := by
  have hcopy := copy_space a bound hb
  have hmiddle := hcopy _ _ le_rfl (compiled_trace (copy_eval a) 330 788)
  have hset : ∀ q z, q≤1 → Trace (compiled restoreHighGuard 330 788) q
      ((copied a).withPC (some (compiled restoreHighGuard 330 788).entry)) z →
      ∀ i, (z.stacks i).length≤bound := by
    intro q z hq hz
    have hcases : q=0 ∨ q=1 := by omega
    rcases hcases with rfl|rfl
    · cases hz; exact hmiddle
    · rw [trace_same_length_unique hz (compiled_trace (restoreHighGuard_eval (copied a)) 330 788)]
      exact hmiddle
  have htail := StructuredSpace.sequence_stack_bound (copy_eval a) (restoreHighGuard_eval (copied a))
    330 788 hcopy hset _ _ _ (compiled_site (.seq copy restoreHighGuard) 330 788)
  have hbody := StructuredSpace.sequence_stack_bound (reset_eval a)
    ((copy_eval a).seq (restoreHighGuard_eval (copied a))) 330 788
    (reset_space a bound hb) htail _ _ _ (compiled_site command 330 788)
  have hsum : (changed.map (fun i => ((clearStacks 792 a.stacks) i).length)).sum≤6*bound := by
    apply (List.sum_le_length_nsmul _ bound (by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      by_cases heq : i=792
      · subst i; simp [clearStacks]
      · simpa [clearStacks,heq] using hb i)).trans_eq
    simp [changed]
  have htime : cost a+1≤21*bound+31 := by
    have ht := hb 792
    have hs := hb 330
    dsimp [cost,resetCost]
    omega
  refine ⟨compiled_halt_trace (command_eval a) 330 788,htime,?_⟩
  exact StructuredSpace.compiled_halt_stack_bound (command_eval a) 330 788 hbody

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
