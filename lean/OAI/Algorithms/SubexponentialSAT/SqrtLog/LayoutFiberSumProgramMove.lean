import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgramBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def move (src dst tmp : Fin 256) : Code :=
  .seq (.call (StackRoutines.copyProgram src dst tmp 0 1))
    (.call (StackRoutines.clearProgram src 0 1))

def moved (src dst : Fin 256) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks src []) dst (a.stacks src)⟩

theorem move_eval (src dst tmp : Fin 256) (a : Data)
    (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst)
    (hd : a.stacks dst=[]) (ht : a.stacks tmp=[]) :
    Eval (move src dst tmp) (9*(a.stacks src).length+8) a (moved src dst a) := by
  have h1 := SubexponentialSAT.SubexpScanPrimitives.copy_eval a src dst tmp 0 1
    hsd hst htd (by decide) ht
  let b := SubexponentialSAT.SubexpScanPrimitives.afterCopy a src dst 0 1
  have h2 := SubexponentialSAT.Subexp.TupleProgram.clear_eval src (0 : Fin 16) 1 b
  have hb : b.stacks src=a.stacks src := by
    simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hsd]
  have he : (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks src b.stacks⟩ : Data)=
      moved src dst a := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i=src
      · subst i; simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
          StackRoutines.clearStacks,StackRoutines.copyStacks,hsd]
      by_cases hj : i=dst
      · subst i; simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
          StackRoutines.clearStacks,StackRoutines.copyStacks,Ne.symm hsd,hd]
      simp [b,SubexponentialSAT.SubexpScanPrimitives.afterCopy,
        StackRoutines.clearStacks,StackRoutines.copyStacks,hi,hj]
  change Eval _ _ b (⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks src b.stacks⟩ : Data) at h2
  rw [he,hb] at h2
  have hcost : 7 * (a.stacks src).length + 5 +
      (2 * (a.stacks src).length + 3) = 9 * (a.stacks src).length + 8 := by omega
  rw [← hcost]
  exact h1.seq h2

def ownerRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
theorem ownerRegisters_injective : Function.Injective ownerRegisters := Fin.castAdd_injective _ _
def ownerStacks : Fin 11 → Fin 256 := ![216,201,217,218,219,220,221,222,223,215,214]
theorem ownerStacks_injective : Function.Injective ownerStacks := by decide
def findOwner : Code := .call (ProgramLinking.liftProgram
  LayoutOwnerFiberProgram.program ownerRegisters ownerStacks)

def ownerResult (a : Data) (regs : Fin 16 → Bool) (is : List ℕ) : Data :=
  ⟨regs,Function.update (Function.update a.stacks 215 (unary is.length)) 214 (encodeIndices is)⟩

theorem findOwner_eval (a : Data) (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : a.stacks 216=unary query)
    (hs : a.stacks 201=LayoutOwnerFiberProgram.stream ps)
    (he : ∀ i : Fin 11, 2 ≤ i.val → a.stacks (ownerStacks i)=[]) :
    ∃ n ≤ LayoutOwnerFiberProgram.budget query ps, ∃ rf,
      Eval findOwner n a
        (ownerResult a rf (LayoutOwnerFiberProgram.fiberIndices query 0 ps)) := by
  obtain ⟨rf,n,hn,ht⟩ := LayoutOwnerFiberProgram.program_runs query ps (a.regs ∘ ownerRegisters)
  have hi : projectState ownerRegisters ownerStacks a=
      LayoutOwnerFiberProgram.data (a.regs ∘ ownerRegisters) (unary query)
        (LayoutOwnerFiberProgram.stream ps) [] [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hh : 2 ≤ i.val
      · have hz := he i hh
        fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
      · fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
  change Trace LayoutOwnerFiberProgram.program n
    ((LayoutOwnerFiberProgram.data (a.regs ∘ ownerRegisters) (unary query)
      (LayoutOwnerFiberProgram.stream ps) [] [] [] [] [] [] [] [] []).withPC
        (some LayoutOwnerFiberProgram.program.entry)) _ at ht
  rw [←hi] at ht
  have hc := eval_call_from_state LayoutOwnerFiberProgram.program ownerRegisters ownerStacks a
    ownerRegisters_injective ownerStacks_injective ht
  let out := LayoutOwnerFiberProgram.data rf (unary query) (LayoutOwnerFiberProgram.stream ps)
    [] [] [] [] [] [] [] (unary (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length)
      (encodeIndices (LayoutOwnerFiberProgram.fiberIndices query 0 ps))
  let rr := (embedState ownerRegisters ownerStacks a out).regs
  have ho : embedState ownerRegisters ownerStacks a out=
      ownerResult a rr (LayoutOwnerFiberProgram.fiberIndices query 0 ps) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hp : ∃ j, ownerStacks j=i
      · obtain ⟨j,rfl⟩ := hp
        have hh := embedState_stack ownerRegisters ownerStacks a out ownerStacks_injective j
        exact hh.trans (by
          by_cases hj : 2 ≤ j.val
          · have hz := he j hj
            fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks]
          · fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks])
      · have hh := embedState_stack_frame ownerRegisters ownerStacks a out i hp
        have h214 : i≠214 := fun h => hp ⟨10,h.symm⟩
        have h215 : i≠215 := fun h => hp ⟨9,h.symm⟩
        exact hh.trans (by simp [h214,h215])
  change Eval findOwner n a (embedState ownerRegisters ownerStacks a out) at hc
  rw [ho] at hc
  exact ⟨n,hn,rr,hc⟩

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
