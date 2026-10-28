import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorBase

namespace OAI.Algorithms

/-! Projection identities are proved before instantiating the numeric query
model, keeping the large generated parameter expression opaque. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp hfield q hv J hJ source hsource

theorem nativeSpecOfInputs_code : e.stacks 281=RingProgram.flat (spec).code := (generatedCode hp).bytes

theorem nativeSpecOfInputs_theta : (spec).p.ops.decode (spec).theta =
    (IrreducibleSearch.data hd).node (m.val 33) s.Q ht hfield s.node := by
  exact RingNodeProgram.nodeCode_decode _ ht hd _ M cache _ hfield s.node

theorem nativeSpecOfInputs_rows : Encoding.encodeList id (spec).rawRows=
    HashScopeProgram.RawTable.inputBits q.width.length q.rows :=
  factorSpec_row_bytes _ _ _ _ _ _ _ _ _ _ _ _ _

theorem nativeSpecOfInputs_parameters :
    (spec).u=m.val 33 ∧ (spec).J=J ∧ (spec).p.R=s.R ∧ (spec).p.aWord=s.height :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem nativeSpecOfInputs_p : (spec).p=
    SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e hp hfield := rfl

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
