import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev zeroProgram : Program 8 13 5 where
  inputStack := 3
  outputStack := 0
  entry := 0
  code := ![.pop 3 0 1 1, .branch 1 2 4, .set 0 false 3, .push 0 0 0, .halt]

def zeroStacks (n : ℕ) (stk : Fin 13 → List Bool) : Fin 13 → List Bool :=
  Function.update (Function.update stk 3 []) 0 (List.replicate n false ++ stk 0)

theorem zeroTrace (count : List Bool) (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool)
    (hc : stk 3=count) :
    Trace zeroProgram (4*count.length+2) ⟨some 0,regs,stk⟩
      ⟨some 4,readRegs regs 0 1 none,zeroStacks count.length stk⟩ := by
  induction count generalizing regs stk with
  | nil =>
      refine .cons (b := ⟨some 1,readRegs regs 0 1 none,Function.update stk 3 []⟩) ?_ ?_
      · simp [step,execInstr,hc]
      · refine .cons (b := ⟨some 4,readRegs regs 0 1 none,zeroStacks 0 stk⟩) ?_ (.refl _)
        simp [step,execInstr,readRegs,zeroStacks]
  | cons bit rest ih =>
      let r1 := readRegs regs 0 1 (some bit)
      let r2 := Function.update r1 0 false
      let s1 := Function.update stk 3 rest
      let s2 := Function.update s1 0 (false::stk 0)
      have ht := ih r2 s2 (by simp [s2,s1])
      have hr : readRegs r2 0 1 none=readRegs regs 0 1 none := by
        funext i; fin_cases i <;> simp [r2,r1,readRegs]
      have hs : zeroStacks rest.length s2=zeroStacks (bit::rest).length stk := by
        funext i; fin_cases i <;> simp [zeroStacks,s2,s1,List.replicate_succ',List.append_assoc]
      rw [hr,hs] at ht
      have he : Trace zeroProgram (4*rest.length+2+4) ⟨some 0,regs,stk⟩
          ⟨some 4,readRegs regs 0 1 none,zeroStacks (bit::rest).length stk⟩ := by
        refine .cons (b := ⟨some 1,r1,s1⟩) ?_ ?_
        · simp [step,execInstr,hc,r1,s1]
        · refine .cons (b := ⟨some 2,r1,s1⟩) ?_ ?_
          · simp [step,execInstr,r1,readRegs]
          · refine .cons (b := ⟨some 3,r2,s1⟩) ?_ ?_
            · simp [step,execInstr,r2]
            · refine .cons (b := ⟨some 0,r2,s2⟩) ?_ ht
              simp [step,execInstr,r2,s2,s1]
      convert he using 1

theorem zero_eval (d : Data) :
    Eval (.call zeroProgram) (4*(d.stacks 3).length+3) d
      ⟨readRegs d.regs 0 1 none,zeroStacks (d.stacks 3).length d.stacks⟩ := by
  apply Eval.call
  have ht := zeroTrace (d.stacks 3) d.regs d.stacks rfl
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  simpa [StructuredProgram.State.withPC,zeroProgram,Nat.add_assoc] using hh

def input (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) : Data :=
  ⟨regs, ![[],[],[],[],[],[],[],[],[],[],indices js,bits,unary n]⟩

def savedInputs (js : List ℕ) (bits : List Bool) (n : ℕ) : Fin 3 → List Bool :=
  ![indices js,bits,unary n]

def initCommand : Code :=
  .seq (.call (StackRoutines.copyProgram 10 2 3 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.copyProgram 11 1 3 (0 : Fin 8) 1))
      (.seq (.call (StackRoutines.copyProgram 12 3 4 (0 : Fin 8) 1))
        (.seq (.call zeroProgram) (Subexp.TupleProgram.pushConst 5 0 true))))

def initCost (js : List ℕ) (bits : List Bool) (n : ℕ) : ℕ :=
  7*(indices js).length+7*bits.length+11*n+20

theorem initCommand_eval (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) :
    ∃ rf, Eval initCommand (initCost js bits n) (input regs js bits n)
      (state rf (savedInputs js bits n) js bits (List.replicate n false)) := by
  let d := input regs js bits n
  have h1 := SubexpScanPrimitives.copy_eval d 10 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  let a := SubexpScanPrimitives.afterCopy d 10 2 0 1
  have h2 := SubexpScanPrimitives.copy_eval a 11 1 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [a,SubexpScanPrimitives.afterCopy,d,input,StackRoutines.copyStacks])
  let b := SubexpScanPrimitives.afterCopy a 11 1 0 1
  have h3 := SubexpScanPrimitives.copy_eval b 12 3 4 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,SubexpScanPrimitives.afterCopy,d,input,StackRoutines.copyStacks])
  let c := SubexpScanPrimitives.afterCopy b 12 3 0 1
  have h4 := zero_eval c
  let e : Data := ⟨readRegs c.regs 0 1 none,zeroStacks (c.stacks 3).length c.stacks⟩
  have h5 := Subexp.TupleProgram.pushConst_eval (5 : Fin 13) (0 : Fin 8) true e
  let f := Subexp.TupleProgram.pushedState (5 : Fin 13) (0 : Fin 8) true e
  have hf : f=state f.regs (savedInputs js bits n) js bits (List.replicate n false) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i; fin_cases i <;>
      simp [e,c,b,a,d,input,savedInputs,
        zeroStacks,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,unary]
  change Eval _ _ e f at h5
  rw [hf] at h5
  refine ⟨f.regs, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 <;>
    simp [initCommand,initCost,c,b,a,d,input,SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks,unary] ; omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
