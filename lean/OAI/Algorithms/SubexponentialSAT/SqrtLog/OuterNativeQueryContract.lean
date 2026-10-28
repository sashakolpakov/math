import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQueryPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeWidth

namespace OAI.Algorithms

/-! Existential widths in the concrete residual context do not become a
uniformity assumption: the same paid trace bounds its output width. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram

 theorem marked_contract_of_polynomial (k CK x y z : ℕ) : ∃ C e : ℕ,
    ∀ (count cost : List Bool → ℕ) (ready : (Fin 763 → List Bool) → Prop)
      (valid : List Bool → Prop),
    (∀ bits tail (base : Query.Data), valid bits → Marked.Wide.invariant ready base →
      ∃ width, Nonempty (LeafOuterNative.PolynomialMarked k CK x y z C e
        (markedStart base tail bits) (count bits) (cost bits) width)) →
    Marked.Wide.QueryValueContract (Query.marked k) count cost (fun bits => cost bits+1)
      ready valid := by
  obtain ⟨C,e,hpoly⟩ := Query.Cost.marked_polynomial k CK x y z
  refine ⟨C,e,?_⟩
  intro count cost ready valid contexts bits tail base hv hb
  let start := markedStart base tail bits
  obtain ⟨width,⟨p⟩⟩ := contexts bits tail base hv hb
  obtain ⟨n,b,hn,he,hs,h320,h322,hvalue,hwidth,h16,h17,h18,h321,h324⟩ :=
    hpoly p.query start p.guard p.V p.L p.preparation p.occurrence p.qi (count bits)
      p.branchBudget width p.context p.queryValid p.clean p.sources p.marked p.reference
      p.zero p.highEmpty p.ambientLarge p.small p.valueCap p.lengthCap p.step p.stepWidth p.referenceBound
  have hn' : n ≤ cost bits := hn.trans p.cost
  have hsource : b.stacks 320=tail := by
    simpa [start,markedStart,RecordPrograms.state,Marked.Wide.recordPorts] using h320
  have hread : Marked.Wide.read b=Marked.Wide.read base := by
    simpa [Marked.Wide.read,start,markedStart,RecordPrograms.state,Marked.Wide.recordPorts] using h322
  have hready : ready (Marked.Wide.workspace b) := by
    rw [hs]
    change ready (Marked.Wide.workspace (markedStart base tail bits))
    rw [marked_start_workspace]
    exact hb.1
  have hstate : RecordPrograms.state Marked.Wide.recordPorts b false true false tail []=b :=
    RecordPrograms.state_eq_self _ b _ _ _ _ _ h16 h17 h18 hsource h321
  have hl := LeafOuterNative.eval_stack_length he 323
  have hl' : (b.stacks 323).length ≤ cost bits+1 := by
    rw [p.zero,List.length_nil] at hl
    omega
  refine ⟨n,b,hn',hready,hread,hvalue,hl',h324,?_⟩
  rw [hstate]
  exact he

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
