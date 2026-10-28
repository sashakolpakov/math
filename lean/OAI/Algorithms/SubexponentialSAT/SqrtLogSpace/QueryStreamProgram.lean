import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

/-! The fixed streaming query runs the actual pair DFS, attained-signature
DFS, two-pass visitor, node readout and canonical count reconstruction. Its
finite command tables have no callback or evaluator parameters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

open OAI BitProgram StructuredCalls
open SignatureTupleProgram SignatureTupleNative
noncomputable section

abbrev Code := Cmd 40 896

/-- The four persistent pair words are separate from the tuple and arithmetic
banks. The callback is permitted to overwrite all five controller registers. -/
def pairPorts : DifferencePairsProgram.Ports 40 896 where
  register := Fin.castAddEmb 35
  stack := {
    toFun := fun i => ⟨832+i.val,by have := i.isLt; omega⟩
    inj' := by
      intro i j h
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 832+i.val=832+j.val at hv
      omega }

/-- Each emitted pair is expanded immediately to ambient Boolean masks. All
attained tuples contribute to851 before its signed value is added to850. -/
def pairCallback : Code :=
  .seq QueryExecution.PairStart.command
    (.seq SignatureTupleComplete.command QueryAssembler.commitPair)

def pairs : Code := DifferencePairsProgram.command pairPorts pairCallback

/-- The native integer-cache bootstrap is reused, without the old tuple
initializer or the old materialized support evaluator. -/
abbrev bootstrapNode : Code := .call (ProgramLinking.liftProgram
  SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort)

/-- One actual framed interpolation node is consumed. The selected node value
and canonical metadata feed every pair; readout is performed after the full
signed node accumulation and appended in increasing node order. -/
abbrev nodeBody : Code :=
  .seq QueryAssembler.Nodes.beginNode
    (.seq NativeLayoutLoad.command
      (.seq bootstrapNode
        (.seq PairNativeSetup.setupCaller
          (.seq pairs QueryNodeFinish.command))))

abbrev nodeLoop : Code := .while 37 nodeBody

/-- The node cursor is copied from the produced table once. A physical peek
initializes the guard; every completed node refreshes it after its callbacks. -/
abbrev nodes : Code :=
  .seq QueryAssembler.Nodes.initializeNodes
    (.seq QueryNodeFinish.guardCursor nodeLoop)

/-- Count one conditioned query. The current high assignment is decoded from
its actual counter word before node evaluation. The final word on323 is read
from the canonical reconstruction, rather than from a count bit. -/
abbrev command : Code :=
  .seq HighQueryAdapter.prepareHigh (.seq nodes QueryReconstruction.command)

def program := compiled command 330 323

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
