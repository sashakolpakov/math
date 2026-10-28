import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedCacheCanonical

namespace OAI.Algorithms

/-! Canonical cache words identify the same native specification independently
of the registers and scratch of a particular head preparation. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
noncomputable section

 theorem native_spec_words_congr
    (s : LeafHeadSetupProgram.Native.Inputs) (m : Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words words' : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (hc' : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words')
    (hw : words=words')
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source) :
    nativeSpecOfInputs s m ht hd words hc M cache half e hp hfield q hv J hJ source hsource =
      nativeSpecOfInputs s m ht hd words' hc' M cache half e hp hfield q hv J hJ source hsource := by
  subst words'
  rfl

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
