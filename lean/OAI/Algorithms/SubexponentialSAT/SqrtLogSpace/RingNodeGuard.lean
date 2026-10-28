import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

/-! A fresh physical peek restores the outer node-loop guard after arbitrary
query callbacks. The encoded cursor is preserved, so `readNode` consumes its
own tag exactly once. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

def peekCursor : Code := .base (.atom (.peek 301 37 38))

def cursorGuarded (a : Data) : Data :=
  ⟨readRegs a.regs 37 38 (a.stacks 301).head?, a.stacks⟩

theorem peekCursor_eval (a : Data) : Eval peekCursor 1 a (cursorGuarded a) :=
  .base (.atom (.peek 301 37 38) a)

theorem peekCursor_frame (a : Data) : (cursorGuarded a).stacks = a.stacks := rfl

theorem peekCursor_test (a : Data) (nodes : List (List Bool))
    (hs : a.stacks 301 = Encoding.encodeList id nodes) :
    (cursorGuarded a).regs 37 = !nodes.isEmpty ∧
    (cursorGuarded a).regs 38 = true := by
  cases nodes <;> simp [cursorGuarded, readRegs, hs, Encoding.encodeList]

theorem peekCursor_resources (a : Data) :
    Trace (compiled peekCursor 301 78) 2
      (a.withPC (some (compiled peekCursor 301 78).entry)) ((cursorGuarded a).withPC none) ∧
    ∀ prefixSteps intermediate, prefixSteps ≤ 2 →
      Trace (compiled peekCursor 301 78) prefixSteps
        (a.withPC (some (compiled peekCursor 301 78).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks+1 :=
  eval_resources (peekCursor_eval a) 301 78

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
