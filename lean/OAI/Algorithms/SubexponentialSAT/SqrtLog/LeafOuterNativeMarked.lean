import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMaskedNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideLength

namespace OAI.Algorithms

/-! An explicit preparation/branch witness for the fixed marked query yields
its streaming collector contract. Every query, including candidates later
rejected by argmin, is present in the charged reference fold. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram

structure MarkedPrepared (k : ℕ) (a : Query.Data) (count budget width : ℕ) where
  query : LeafQueryFrontend.Query
  guard : Guard (query.input k)
  W : ℕ
  V : ℕ
  L : ℕ
  preparation : Query.Preparation query k (Query.markedInput (Query.Carried.reference a)) guard W V L
  clean : Query.CleanWork a
  initialWidth : ∀ i, ((Query.markedInput (Query.Carried.reference a)).stacks i).length ≤ W
  branchBudget : ℕ
  context : Marked.Wide.BranchContext Residual.command
    (Marked.Wide.maskCopied (Query.prepared preparation.out))
    (Query.ProtectedWork (Query.Carried.reference a)) count branchBudget width
  cost : 10*(a.stacks 321).length+10+Query.preparationBudget preparation branchBudget ≤ budget

theorem marked_value_contract (k : ℕ) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (contexts : ∀ bits tail (base : Query.Data), valid bits → Marked.Wide.invariant ready base →
      Nonempty (MarkedPrepared k
        (RecordPrograms.state Marked.Wide.recordPorts base false true false tail bits.reverse)
        (count bits) (queryCost bits) (width bits))) :
    Marked.Wide.QueryValueContract (Query.marked k) count queryCost width ready valid := by
  intro bits tail base hv hb
  let start := RecordPrograms.state Marked.Wide.recordPorts base false true false tail bits.reverse
  obtain ⟨p⟩ := contexts bits tail base hv hb
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    Query.Carried.marked_from_masked_preparation p.query k start p.guard p.W p.V p.L
      p.preparation p.clean p.initialWidth (count bits) p.branchBudget (width bits) p.context
  have hsource : b.stacks 320=tail := by
    simpa [start,RecordPrograms.state,Marked.Wide.recordPorts] using h320
  have hread : Marked.Wide.read b=Marked.Wide.read base := by
    simpa [Marked.Wide.read,start,RecordPrograms.state,Marked.Wide.recordPorts] using h322
  have hready : ready (Marked.Wide.workspace b) := by
    rw [hs,Marked.Wide.workspace_recordState]
    exact hb.1
  have hstate : RecordPrograms.state Marked.Wide.recordPorts b false true false tail []=b :=
    RecordPrograms.state_eq_self _ b _ _ _ _ _ h16 h17 h18 hsource h321
  refine ⟨n,b,hn.trans p.cost,hready,hread,hv,hl,h324,?_⟩
  rw [hstate]
  exact he

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
