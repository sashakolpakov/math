import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([12,16,17,18,19,20,21,34,36,40,42] : List (Fin 64)), d.stacks i = []

def addressed (d : Data) : Data := afterCopy (afterCopy d 31 40 0 1) 39 40 0 1
def address : Code := .seq (copy 31 40) (copy 39 40)

theorem address_eval (d : Data) (h42 : d.stacks 42 = []) :
    Eval address (7 * (d.stacks 31).length + 7 * (d.stacks 39).length + 10)
      d (addressed d) := by
  have h1 := copy_eval d 31 40 42 0 1 (by decide) (by decide) (by decide) (by decide) h42
  have h2 := copy_eval (afterCopy d 31 40 0 1) 39 40 42 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [afterCopy, StackRoutines.copyStacks, h42])
  convert h1.seq h2 using 1 <;>
    simp [address, addressed, copy, Subexp.SupportSelectionProgram.copy, afterCopy,
      StackRoutines.copyStacks] ; try omega

def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 40 []⟩
def clearAddress : Code := .call (StackRoutines.clearProgram 40 0 1)

def test : Code := .seq address (.seq lookup (.seq clearAddress
  (.seq (copy 32 12) (HeadIdentifierProgram.readBit false))))

def tested (d : Data) (answer : Bool) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) 4 answer, d.stacks⟩

def testCost (A j W : ℕ) (bitIndex word : List Bool) : ℕ :=
  lookupCost (A + j) W + 9 * (A + j) + 7 * bitIndex.length + 18 +
    Subexp.TypeBitProgram.cost bitIndex word

theorem test_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
    (hi : (d.stacks 31).length + (d.stacks 39).length = earlier.length)
    (hw : word.length = (d.stacks 38).length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
    Eval test (testCost (d.stacks 31).length (d.stacks 39).length
      (d.stacks 38).length (d.stacks 32) word)
      d (tested d (word.getD (d.stacks 32).length false)) := by
  have hz12 := hc 12 (by decide)
  have hz36 := hc 36 (by decide)
  have hz40 := hc 40 (by decide)
  have hz42 := hc 42 (by decide)
  let a := addressed d
  have h1 := address_eval d hz42
  let b := selected a word
  have h2 : Eval lookup (lookupCost ((d.stacks 31).length + (d.stacks 39).length)
      (d.stacks 38).length) a b := by
    have he := lookup_eval a earlier word rest
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hs)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks, hz40, Nat.add_comm] using hi)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hw)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hr)
      (by
        intro i hi'
        have h40 : i ≠ 40 := by intro he; subst i; simp at hi'
        simpa [a, addressed, afterCopy, StackRoutines.copyStacks, h40] using
          hc i (by simp at hi' ⊢; tauto))
    simpa [b, a, addressed, afterCopy, StackRoutines.copyStacks, hz40, ← hi, Nat.add_comm] using he
  let c := cleared b
  have h3 : Eval clearAddress (2 * ((d.stacks 31).length + (d.stacks 39).length) + 3) b c := by
    simpa [clearAddress, c, cleared, b, selected, a, addressed, afterCopy,
      StackRoutines.copyStacks, StackRoutines.clearStacks, hz40, Nat.add_comm] using
      Subexp.TupleProgram.clear_eval (40 : Fin 64) (0 : Fin 16) 1 b
  let e := afterCopy c 32 12 0 1
  have h4 : Eval (copy 32 12) (7 * (d.stacks 32).length + 5) c e := by
    have he := copy_eval c 32 12 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [c, cleared, b, selected, a, addressed, afterCopy, StackRoutines.copyStacks, hz42])
    simpa [e, c, cleared, b, selected, a, addressed, copy,
      Subexp.SupportSelectionProgram.copy, afterCopy,
      StackRoutines.copyStacks] using he
  let z := HeadIdentifierProgram.bitResult e false (word.getD (d.stacks 32).length false)
  have h5 : Eval (HeadIdentifierProgram.readBit false)
      (Subexp.TypeBitProgram.cost (d.stacks 32) word) e z := by
    simpa [z, e, c, cleared, b, selected, a, addressed, afterCopy,
      StackRoutines.copyStacks, HeadIdentifierProgram.bitSource, hz12] using
      HeadIdentifierProgram.readBit_eval e false
  have heq : z = tested d (word.getD (d.stacks 32).length false) := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
        HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitFlag, tested, readRegs]
    · funext i
      by_cases h12 : i = 12
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz12]
      by_cases h36 : i = 36
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz36]
      by_cases h40 : i = 40
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz40]
      · simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, h12, h36, h40]
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  rw [heq] at he
  convert he using 1 <;> simp [test, testCost] ; omega

theorem testCost_bound (A j W : ℕ) (bitIndex word : List Bool) (hw : word.length = W) :
    testCost A j W bitIndex word ≤
      lookupCost (A + j) W + 9 * (A + j) + 10 * bitIndex.length + 2 * W + 24 := by
  have h := Subexp.TypeBitProgram.cost_le bitIndex word
  unfold testCost
  omega

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
