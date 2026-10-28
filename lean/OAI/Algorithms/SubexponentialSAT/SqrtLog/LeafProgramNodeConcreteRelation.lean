import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

/-! Changing a valid reconstruction of the head coefficient cache does not
change the same-node assignment relation or the assembly parameters. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing LeafParametersProgram

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (wi wj : List (List Bool))
    (hi : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width wi)
    (hj : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width wj)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hf : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)

 theorem nativeSpec_relation_independent (high bits : List Bool)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 (m.val 33))) (m.val 34)) :
    AssignmentConcrete.relation
      (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs)
      high bits headIds zero one =
    AssignmentConcrete.relation
      (PreparedSource.nativeSpecOfInputs s m ht hd wj hj M cache half e hp hf q hv J hJ source hs)
      high bits headIds zero one := by
  rfl

 theorem nativeSpec_table_independent :
    (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs).ctx.table =
    (PreparedSource.nativeSpecOfInputs s m ht hd wj hj M cache half e hp hf q hv J hJ source hs).ctx.table := by
  rfl

 theorem nativeSpec_one_independent :
    (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs).one =
    (PreparedSource.nativeSpecOfInputs s m ht hd wj hj M cache half e hp hf q hv J hJ source hs).one := by
  rfl

 theorem nativeSpec_degree_parameters :
    (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs).p.R=s.R ∧
    (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs).p.t=m.val 33 ∧
    (PreparedSource.nativeSpecOfInputs s m ht hd wi hi M cache half e hp hf q hv J hJ source hs).J=J := by
  exact ⟨rfl,rfl,rfl⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
