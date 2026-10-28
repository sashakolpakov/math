import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramUniversalEntry
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgramEntrySemantics

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Saved := LayoutProgramScalar.FromCounts.Saved
abbrev Data := State 10 64

variable {r Q : ℕ}

def baseStacks (c : Saved) (t : Fin Q) (u y : UniversalType r Q 1) : Fin 64 → List Bool :=
  fun j => if hj : j.val < 42 then
    (Guard.guardInput (0 : Fin 1) t u y [] [] [] [] (fun _ => false)).stacks ⟨j.val,hj⟩
  else if j=42 then c.hp else if j=43 then c.hn else if j=44 then c.width
  else if j=45 then c.power.1 else if j=46 then c.power.2 else if j=47 then c.r
  else if j=48 then c.a else []

def state (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) (result : WordPair) : Data :=
  ⟨regs,Function.update (Function.update (Function.update (Function.update
    (baseStacks c t u y) 2 uc) 3 hc) 50 result.1) 51 result.2⟩

abbrev guarded : Cmd 10 64 := .seq ScanRestore.command (.ite 7 scalar clearCounts)
abbrev command : Cmd 10 64 := .seq guard (.ite 9 guarded (.base .skip))
def program := compiled command 23 50

theorem guard_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    projectState id guardPorts (state c regs t u y [] [] ([],[])) =
      Guard.guardInput (0 : Fin 1) t u y [] [] [] [] regs := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [guardPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

theorem scan_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    projectState ScanRestore.scanRegisters ScanRestore.scanPorts (state c regs t u y [] [] ([],[])) =
      Scan.scanInput (0 : Fin 1) u y [] [] [] [] (regs ∘ ScanRestore.scanRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [ScanRestore.scanPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

theorem scalar_project (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    projectState scalarRegs scalarPorts (state c regs t u y uc hc ([],[])) =
      LayoutProgramScalar.FromCounts.state c (regs ∘ scalarRegs) uc hc [] [] [] [] [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  fin_cases j <;> simp [scalarPorts,state,baseStacks,Guard.guardInput,
    Scan.scanInput,MatrixEntryProgram.input]

theorem scalar_embed (c : Saved) (regs : Fin 10 → Bool) (rr : Fin 9 → Bool)
    (t : Fin Q) (u y : UniversalType r Q 1) (uc hc : List Bool) (result : WordPair) :
    let start := state c regs t u y uc hc ([],[])
    let out := LayoutProgramScalar.FromCounts.state c rr [] [] [] [] [] [] [] result
    let e := embedState scalarRegs scalarPorts start out
    e = state c e.regs t u y [] [] result := by
  intro start out e
  apply embedState_eq_of_ports scalarRegs scalarPorts _ _ _ scalarRegs_inj scalarPorts_inj
  · intro j; exact embedState_register scalarRegs scalarPorts start out scalarRegs_inj j
  · intro j hj; exact embedState_register_frame scalarRegs scalarPorts start out j hj
  · intro j
    fin_cases j <;> simp [out,state,baseStacks,scalarPorts,Guard.guardInput,Scan.scanInput,
      MatrixEntryProgram.input,LayoutProgramScalar.FromCounts.state]
  · intro j hj
    have h2 : j ≠ 2 := by
      intro h; exact hj ⟨7,(show scalarPorts 7=2 by decide).trans h.symm⟩
    have h3 : j ≠ 3 := by
      intro h; exact hj ⟨8,(show scalarPorts 8=3 by decide).trans h.symm⟩
    have h50 : j ≠ 50 := by
      intro h; exact hj ⟨37,(show scalarPorts 37=50 by decide).trans h.symm⟩
    have h51 : j ≠ 51 := by
      intro h; exact hj ⟨38,(show scalarPorts 38=51 by decide).trans h.symm⟩
    simp [start,state,h2,h3,h50,h51]

theorem clearCounts_eval (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    ∃ rf, Eval clearCounts (2*uc.length+2*hc.length+6)
      (state c regs t u y uc hc ([],[])) (state c rf t u y [] [] ([],[])) := by
  let s := state c regs t u y uc hc ([],[])
  let s₁ : Data := ⟨readRegs regs 0 1 none,StackRoutines.clearStacks 2 s.stacks⟩
  let s₂ : Data := ⟨readRegs s₁.regs 0 1 none,StackRoutines.clearStacks 3 s₁.stacks⟩
  have h₁ := Subexp.TupleProgram.clear_eval 2 0 1 s
  have h₂ := Subexp.TupleProgram.clear_eval 3 0 1 s₁
  have hs : s₂ = state c s₂.regs t u y [] [] ([],[]) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
      simp [s₁,s,state,StackRoutines.clearStacks,Function.update_apply,h2,h3]
  have hh := h₁.seq h₂
  change Eval clearCounts _ s s₂ at hh
  rw [hs] at hh
  refine ⟨s₂.regs,?_⟩
  convert hh using 1 ; simp [s₁,s,state,StackRoutines.clearStacks] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
