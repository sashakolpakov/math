import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing LeafParametersProgram
noncomputable section

theorem nativeSpec_degree_of_budget
    (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hf : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (k factors : ℕ)
    (hwidth : ∀ c ∈ source, c.length ≤ k) (hfactors : q.rows.length ≤ factors)
    (hbudget : k*s.R*(2*factors+3*(m.val 33-1)+1) < s.Q*J) :
    (specTarget (PreparedSource.nativeSpecOfInputs s m ht hd words hc M cache half e hp hf q hv J hJ source hs) H high).natDegree < s.Q*J := by
  apply specTarget_degree_of_budget (PreparedSource.nativeSpecOfInputs s m ht hd words hc M cache half e hp hf q hv J hJ source hs) H high k factors hwidth
  · change (PreparedSource.castRows (congrArg List.length hs) q.rows).length ≤ factors
    rw [PreparedSource.castRows_length]
    exact hfactors
  · exact hbudget

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end OAI.Algorithms
