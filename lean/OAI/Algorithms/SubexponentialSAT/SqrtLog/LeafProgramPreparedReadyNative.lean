import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

/-! The generic physical preparation theorem specializes to the actual
source specification with no packing, cache, or plan alignment premises. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open NodeNative LeafHeadSetupProgram PreparedSource
noncomputable section

 theorem preparation_native_facts
    {s : HeadInputs} {a b : NodeNative.Data} (pr : Preparation s a b) (ha : Ready s a)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hm : FactorStatic (nativeSpecOfInputs s m ht hd pr.head.words pr.head.cache
      M cache half e hp hfield q hv J hJ source hsource) a) :
    NodeFacts (nativeSpecOfInputs s m ht hd pr.head.words pr.head.cache
      M cache half e hp hfield q hv J hJ source hsource) b.stacks := by
  apply preparation_facts pr ha _ hm rfl rfl rfl rfl rfl rfl
  · change SelectorProgram.rawRecords (EntryBank.metadataRecords s.packing) =
      SelectorProgram.rawRecords (PackingMetadata.records
        (PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing)
        (fun v=>List.replicate v.val true) CollisionProgram.encodeType)
    rw [PackingIncidenceInput.reindexPacking_metadataBytes]
    rfl
  · rfl
  · rfl

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
