import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

/-! The specified query target is shared by every interpolation node and by
all valid physical reconstructions of the head coefficient cache. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT MulticolorTypes SubexpLiftRing SubexpQuarticRing LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ) (hg : Guard (q.input k))
variable (first : Word ((Query.packingProblem q k hg)).r ((Query.packingProblem q k hg)).Q) (tail : List (Word ((Query.packingProblem q k hg)).r ((Query.packingProblem q k hg)).Q))
    (i j : Fin ((Query.packingProblem q k hg)).Q)
variable (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (wi wj : List (List Bool))
    (hi : LeafHeadSetupProgram.CacheCorrect ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i)).height (LeafHeadSetupProgram.unary ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i)).R) ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i)).width wi)
    (hj : LeafHeadSetupProgram.CacheCorrect ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail j)).height (LeafHeadSetupProgram.unary ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail j)).R) ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail j)).width wj)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33)) (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hf : ((Query.packingProblem q k hg)).Q < 3^(m.val 34)) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin ((Query.packingProblem q k hg)).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)

include q hv k hg first tail i j m ht hd wi wj hi hj M cache half e hp hf J hJ source hs

 theorem query_target_independent (H : Finset (Fin ((Query.packingProblem q k hg)).n)) (high : H → Bool) :
    specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs) H high=specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail j) m ht hd wj hj M cache half e hp hf q hv J hJ source hs) H high := by
  rfl

omit hj j wj in
 theorem query_target_count (H : Finset (Fin ((Query.packingProblem q k hg)).n)) (high : H → Bool) :
    (specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs) H high).eval 0=
      (NodeSemantics.ternaryFixedHighCount H high (sourceHashes (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs)) ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs)).marked ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs)).markedClause : ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs)).p.model.O ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs)).p.t) := by
  exact specTarget_count (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd wi hi M cache half e hp hf q hv J hJ source hs) (PreparedSource.generatedCode hp).modulus
    (PreparedSource.generatedCode hp).cache (PreparedSource.generatedCode hp).half rfl
    (PreparedSource.generatedCode hp).inverse H high

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
