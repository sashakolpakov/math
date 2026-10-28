import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarStep
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramCount
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

abbrev Data := State 9 40

structure Saved where
  hp : List Bool
  hn : List Bool
  width : List Bool
  power : WordPair
  r : List Bool
  a : List Bool

def state (c : Saved) (regs : Fin 9 → Bool)
    (unchanged h n rc ac bp bn : List Bool) (result : WordPair) : Data :=
  ⟨regs,![c.hp,c.hn,c.width,c.power.1,c.power.2,c.r,c.a,unchanged,h,n,rc,ac,bp,bn,
    [],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],result.1,result.2,[]]⟩

def regs2 : Fin 2 → Fin 9 := Fin.castAdd 7
def regs8 : Fin 8 → Fin 9 := Fin.castAdd 1
def countPorts : Fin 2 → Fin 40 := ![9,7]
def binomialPorts : Fin 20 → Fin 40 :=
  ![12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,8,10,2]
def numeratorPorts : Fin 25 → Fin 40 :=
  ![0,1,12,13,2,3,4,9,14,15,16,17,18,19,20,21,22,23,24,11,25,26,27,37,38]

theorem regs2_injective : Function.Injective regs2 := Fin.castAdd_injective _ _
theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective _ _
theorem countPorts_injective : Function.Injective countPorts := by decide
theorem binomialPorts_injective : Function.Injective binomialPorts := by decide
theorem numeratorPorts_injective : Function.Injective numeratorPorts := by decide

abbrev copy (src dst : Fin 40) : Cmd 9 40 :=
  .call (StackRoutines.copyProgram src dst 14 0 1)
abbrev copies : Cmd 9 40 := .seq (copy 5 9) (.seq (copy 5 10) (copy 6 11))
abbrev count : Cmd 9 40 := .call (ProgramLinking.liftProgram LayoutProgram.Count.program regs2 countPorts)
abbrev clear (src : Fin 40) : Cmd 9 40 := .call (StackRoutines.clearProgram src 0 1)
abbrev cleanup : Cmd 9 40 := .seq (clear 12) (clear 13)

theorem copies_eval (c : Saved) (regs : Fin 9 → Bool) (u h : List Bool) :
    ∃ rf, Eval copies (14*c.r.length+7*c.a.length+15)
      (state c regs u h [] [] [] [] [] ([],[]))
      (state c rf u h c.r c.r c.a [] [] ([],[])) := by
  let s := state c regs u h [] [] [] [] [] ([],[])
  let s₁ := SubexpScanPrimitives.afterCopy s 5 9 0 1
  let s₂ := SubexpScanPrimitives.afterCopy s₁ 5 10 0 1
  let s₃ := SubexpScanPrimitives.afterCopy s₂ 6 11 0 1
  have h₁ := SubexpScanPrimitives.copy_eval s 5 9 14 0 1 (by decide) (by decide) (by decide) (by decide) (by rfl)
  have h₂ := SubexpScanPrimitives.copy_eval s₁ 5 10 14 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state])
  have h₃ := SubexpScanPrimitives.copy_eval s₂ 6 11 14 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state])
  have he : s₃ = state c s₃.regs u h c.r c.r c.a [] [] ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state]
  refine ⟨s₃.regs,?_⟩
  have hh := h₁.seq (h₂.seq h₃)
  change Eval copies _ s s₃ at hh
  rw [he] at hh
  convert hh using 1 ; simp [s₂,s₁,s,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,state] ; omega

theorem count_eval (c : Saved) (regs : Fin 9 → Bool) (h rc ac : List Bool) (R d : ℕ) :
    ∃ t ≤ 3*d+4, ∃ rf, Eval count t
      (state c regs (List.replicate (d+1) true) h (List.replicate R true) rc ac [] [] ([],[]))
      (state c rf [] h (List.replicate (R-d) true) rc ac [] [] ([],[])) := by
  let start := state c regs (List.replicate (d+1) true) h (List.replicate R true) rc ac [] [] ([],[])
  obtain ⟨t,ht,rf,he⟩ := LayoutProgram.Count.command_eval (regs ∘ regs2) R d
  have hp : projectState regs2 countPorts start =
      LayoutProgram.Count.state (regs ∘ regs2) (List.replicate R true) (List.replicate (d+1) true) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [start,state,countPorts]
  have hh := eval_call_from_state LayoutProgram.Count.program regs2 countPorts start
    regs2_injective countPorts_injective (by rw [hp]; exact compiled_halt_trace he 0 0)
  let target := embedState regs2 countPorts start (LayoutProgram.Count.state rf (List.replicate (R-d) true) [])
  have hf : target = state c target.regs [] h (List.replicate (R-d) true) rc ac [] [] ([],[]) := by
    apply embedState_eq_of_ports regs2 countPorts _ _ _ regs2_injective countPorts_injective
    · intro i; exact embedState_register regs2 countPorts start
        (LayoutProgram.Count.state rf (List.replicate (R-d) true) []) regs2_injective i
    · intro i hi; exact embedState_register_frame regs2 countPorts start
        (LayoutProgram.Count.state rf (List.replicate (R-d) true) []) i hi
    · intro i; fin_cases i <;> simp [state,countPorts]
    · intro i hi
      have hn : i≠9 ∧ i≠7 := by
        constructor
        · intro e; apply hi; exact ⟨0,e.symm⟩
        · intro e; apply hi; exact ⟨1,e.symm⟩
      fin_cases i <;> simp_all [start,state]
  change Eval count (t+1) start target at hh
  rw [hf] at hh
  exact ⟨t+1,by omega,target.regs,hh⟩

theorem cleanup_eval (c : Saved) (regs : Fin 9 → Bool) (bp bn : List Bool) (result : WordPair) :
    ∃ rf, Eval cleanup (2*bp.length+2*bn.length+6)
      (state c regs [] [] [] [] [] bp bn result)
      (state c rf [] [] [] [] [] [] [] result) := by
  let s := state c regs [] [] [] [] [] bp bn result
  let s₁ : Data := ⟨readRegs regs 0 1 none,StackRoutines.clearStacks 12 s.stacks⟩
  let s₂ : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 13 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 12 0 1 s
  have h₂ := Subexp.TupleProgram.clear_eval 13 0 1 s₁
  have he : s₂ = state c s₂.regs [] [] [] [] [] [] [] result := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [s₁,s,StackRoutines.clearStacks,state]
  have hh := h₁.seq h₂
  change Eval cleanup _ s s₂ at hh
  rw [he] at hh
  refine ⟨s₂.regs,?_⟩
  convert hh using 1 ; simp [s₁,s,StackRoutines.clearStacks,state] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
