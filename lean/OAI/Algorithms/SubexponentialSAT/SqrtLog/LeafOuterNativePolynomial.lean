import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostFinal

namespace OAI.Algorithms

/-! Direct use of the uniform polynomial native-query theorem. The witness
contains preparation/provenance and residual contracts, never an Eval premise.
Its source-width bound keeps the caller's literal padding and reference bits. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram ProducedQueryResources

structure PolynomialMarked (k CK x y z C e : ℕ) (a : Query.Data) (count budget width : ℕ) where
  query : LeafQueryFrontend.Query
  guard : Guard (query.input k)
  V : ℕ
  L : ℕ
  preparation : Query.Preparation query k (Query.markedInput (Query.Carried.reference a)) guard
    (Query.Carried.markedWidth a) V L
  occurrence : ℕ
  qi : ℕ
  branchBudget : ℕ
  context : Marked.Wide.BranchContext Residual.command
    (Marked.Wide.maskCopied (Query.prepared preparation.out))
    (Query.ProtectedWork (Query.Carried.reference a)) count branchBudget width
  queryValid : query.Valid
  clean : Query.CleanWork a
  sources : Query.Sources query a
  marked : query.mark.isSome=true
  reference : a.stacks 321=query.index.reverse
  zero : a.stacks 323=[]
  highEmpty : ∀ i : Fin 768, 744 ≤ i.val → a.stacks i=[]
  ambientLarge : 2 ≤ ambient query
  small : SmallInputs query k (ambient query)
  valueCap : V=Query.modelValueCap (Circuit.result Serialization.code
    (Execute.guardedModel (query.input k) preparation.lengths))
  lengthCap : L=Query.modelLengthCap (Circuit.result Serialization.code
    (Execute.guardedModel (query.input k) preparation.lengths))
  step : context.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap preparation occurrence qi)
    (Query.Cost.nodeCap preparation occurrence qi CK x y z)
  stepWidth : context.stepWidth ≤ Query.Cost.ordinaryCap preparation occurrence qi
  referenceBound : context.referenceBound ≤ Query.Cost.ordinaryCap preparation occurrence qi
  cost : C*(Query.Carried.sourceBytes a+1)^e*(ambient query+1)^((ordinaryExponent+1)*e)*
    (CostAssembly.assembledWork k (ambient query)
      (ProducedQueryResources.resources query k occurrence qi guard preparation.firstWord preparation.remainingWords)+1)^e ≤ budget

theorem marked_polynomial_contract (k CK x y z : ℕ) : ∃ C e : ℕ,
    ∀ (count queryCost width : List Bool → ℕ) (ready : (Fin 763 → List Bool) → Prop)
      (valid : List Bool → Prop),
    (∀ bits tail (base : Query.Data), valid bits → Marked.Wide.invariant ready base →
      Nonempty (PolynomialMarked k CK x y z C e
        (RecordPrograms.state Marked.Wide.recordPorts base false true false tail bits.reverse)
        (count bits) (queryCost bits) (width bits))) →
    Marked.Wide.QueryValueContract (Query.marked k) count queryCost width ready valid := by
  obtain ⟨C,e,hpoly⟩ := Query.Cost.marked_polynomial k CK x y z
  refine ⟨C,e,?_⟩
  intro count queryCost width ready valid contexts bits tail base hv hb
  let start := RecordPrograms.state Marked.Wide.recordPorts base false true false tail bits.reverse
  obtain ⟨p⟩ := contexts bits tail base hv hb
  obtain ⟨n,b,hn,he,hs,h320,h322,hv,hl,h16,h17,h18,h321,h324⟩ :=
    hpoly p.query start p.guard p.V p.L p.preparation p.occurrence p.qi (count bits)
      p.branchBudget (width bits) p.context p.queryValid p.clean p.sources p.marked p.reference
      p.zero p.highEmpty p.ambientLarge p.small p.valueCap p.lengthCap p.step p.stepWidth p.referenceBound
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
