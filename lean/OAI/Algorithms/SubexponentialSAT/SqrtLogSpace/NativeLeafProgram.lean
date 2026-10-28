import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch

/-! One fixed counting leaf, parameterized only by the fixed clause width.
The actual candidate queries and the separate history-only final query are
installed in the native greedy run. Terminal outer formulas use the checked
zero/power-of-two dispatcher. Semantic and resource composition is proved
separately; this file introduces no callback or evaluator parameter. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram

open BitProgram StructuredCalls
noncomputable section

/-- Physical preparation, all staged marked-query rounds, then the distinct
history-only accepted count. The full canonical result is written on788. -/
def localCommand (k : ℕ) : Cmd 40 896 :=
  NativeLeafRun.command (HighQueryProgram.marked k) (HighQueryProgram.accepted k)

def localProgram (k : ℕ) := compiled (localCommand k) 784 788

/-- Outer terminal classification retains ambient n. A nonterminal call
loads the disjoint leaf bank, executes the fixed local program, copies its
whole count to263, and physically clears the leaf bank before returning. -/
def command (k : ℕ) : Cmd 80 1220 :=
  NativeLeafDispatch.command (NativeLeafExecution.command (localCommand k))

def program (k : ℕ) := compiled (command k) 265 263

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram
