import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- Inputs 31/32/33/38/39 are low mask, bit index, flat head-word table,
word width and original variable index. Scratch is restored after the test. -/
def Clean (d : Data) : Prop :=
  ∀ i ∈ ([12,13,16,17,18,19,20,21,34,36,42] : List (Fin 64)),d.stacks i=[]

def test : Code := .seq (copy 39 12) (.seq (copy 31 13) (.seq (readBit true)
  (.seq lookup (.seq (copy 32 12) (readBit false)))))

def tested (d : Data) (low head : Bool) : Data :=
  ⟨Function.update (Function.update (readRegs d.regs 0 1 none) 6 low) 4 head,d.stacks⟩

def testCost (index low bitIndex word : List Bool) (W : ℕ) : ℕ :=
  (7*index.length+5)+(7*low.length+5)+Subexp.TypeBitProgram.cost index low+
    lookupCost index.length W+(7*bitIndex.length+5)+Subexp.TypeBitProgram.cost bitIndex word

theorem test_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 39).length=earlier.length)
    (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
    Eval test (testCost (d.stacks 39) (d.stacks 31) (d.stacks 32) word (d.stacks 38).length)
      d (tested d ((d.stacks 31).getD (d.stacks 39).length false)
        (word.getD (d.stacks 32).length false)) := by
  have hz12 := hc 12 (by decide)
  have hz13 := hc 13 (by decide)
  have hz36 := hc 36 (by decide)
  have hz42 := hc 42 (by decide)
  let a := afterCopy d 39 12 0 1
  have h1 : Eval (copy 39 12) (7*(d.stacks 39).length+5) d a :=
    copy_eval d 39 12 42 0 1 (by decide) (by decide) (by decide) (by decide) hz42
  let b := afterCopy a 31 13 0 1
  have h2 : Eval (copy 31 13) (7*(d.stacks 31).length+5) a b := by
    have he := copy_eval a 31 13 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [a,afterCopy,StackRoutines.copyStacks,hz42])
    simpa [copy, Subexp.SupportSelectionProgram.copy, b, a, afterCopy,
      StackRoutines.copyStacks] using he
  let c := bitResult b true ((d.stacks 31).getD (d.stacks 39).length false)
  have h3 : Eval (readBit true) (Subexp.TypeBitProgram.cost (d.stacks 39) (d.stacks 31)) b c := by
    simpa [c,b,a,afterCopy,StackRoutines.copyStacks,bitSource,hz12,hz13] using readBit_eval b true
  let e := selected c word
  have h4 : Eval lookup (lookupCost (d.stacks 39).length (d.stacks 38).length) c e := by
    have he := lookup_eval c earlier word rest
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hs)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hi)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hw)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hr)
      (by
        intro i hi'
        have hi12 : i ≠ 12 := by intro he; subst i; simp at hi'
        have hi13 : i ≠ 13 := by intro he; subst i; simp at hi'
        simp [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hi12,hi13,
          hc i (by simp at hi' ⊢; tauto)])
    simpa [e,c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hi] using he
  let f := afterCopy e 32 12 0 1
  have h5 : Eval (copy 32 12) (7*(d.stacks 32).length+5) e f := by
    have he := copy_eval e 32 12 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [e,c,b,a,selected,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hz42])
    simpa [copy, Subexp.SupportSelectionProgram.copy, f, e, c, b, a, selected,
      bitResult, bitSource, afterCopy,
      StackRoutines.copyStacks] using he
  let z := bitResult f false (word.getD (d.stacks 32).length false)
  have h6 : Eval (readBit false) (Subexp.TypeBitProgram.cost (d.stacks 32) word) f z := by
    simpa [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,StackRoutines.copyStacks]
      using readBit_eval f false
  have hz : z=tested d ((d.stacks 31).getD (d.stacks 39).length false)
      (word.getD (d.stacks 32).length false) := by
    apply state_ext
    · funext i; fin_cases i <;>
        simp [z,f,e,c,b,a,selected,bitResult,bitFlag,afterCopy,tested,readRegs]
    · funext i
      by_cases h12 : i=12
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz12]
      by_cases h13 : i=13
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz13]
      by_cases h36 : i=36
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz36]
      · simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,h12,h13,h36]
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [hz] at he
  simpa [test,testCost,Nat.add_assoc] using he

theorem testCost_bound (index low bitIndex word : List Bool) (W : ℕ)
    (hw : word.length=W) :
    testCost index low bitIndex word W ≤ lookupCost index.length W+
      10*index.length+9*low.length+10*bitIndex.length+2*W+27 := by
  have h1 := Subexp.TypeBitProgram.cost_le index low
  have h2 := Subexp.TypeBitProgram.cost_le bitIndex word
  unfold testCost
  omega

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
