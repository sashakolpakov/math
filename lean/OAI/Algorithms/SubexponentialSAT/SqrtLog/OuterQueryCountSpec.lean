import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterQueryCountFormula
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSpec

namespace OAI.Algorithms

/-! The actual source/mark fields of factorSpec determine the selector count;
its arithmetic and packing fields do not add an acceptance condition. -/
namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram LeafOuterProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.MulticolorTypes
open Subexp.ConstructivePacking LayoutProgram
noncomputable section

theorem factorSpec_sourceHashes {r Q n d : ℕ}
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin n))))
    (hc : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    NodeConcrete.sourceHashes (PreparedSource.factorSpec p ps P q hv J hJ source hc theta width hw code) =
    rawHashes (fun i => HashInputProgram.Expansion.originalClause source
      (Fin.cast (congrArg List.length hc) i)) q.rows := by
  simp only [NodeConcrete.sourceHashes,PreparedSource.factorSpec,PreparedSource.castRows,
    rawHashes,List.map_map,Function.comp_def]

def payloadRows {n : ℕ} (F : Formula n) (width : ℕ)
    (hm : 0 < (formulaRecords F).length) (payloads : List (List Bool)) :=
  payloads.map (LeafScopeResourceBounds.rawDecode (formulaRecords F).length width hm)

theorem factorSpec_selectorCount {n N B r Q d : ℕ}
    (F : Formula n) (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width : ℕ) (hm : 0 < (formulaRecords F).length) (payloads : List (List Bool))
    (mark : Option (Fin (formulaRecords F).length))
    (hN : N=ProducedQueryResources.ambient (query F a (payloadRows F width hm payloads) mark))
    (hv : (query F a (payloadRows F width hm payloads) mark).Valid)
    (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J : ℕ) (hJ : 0 < J) (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (scalarWidth : List Bool) (hw : scalarWidth.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    let source := querySource F a ha (payloadRows F width hm payloads) mark N hN
    let spec := PreparedSource.factorSpec p ps P
      (query F a (payloadRows F width hm payloads) mark) hv J hJ source
      (querySource_bytes F a ha (payloadRows F width hm payloads) mark N hN)
      theta scalarWidth hw code
    PreparedBranchCount.fullCount (NodeConcrete.sourceHashes spec) spec.marked spec.markedClause =
      selectorCount F width payloads mark := by
  have hn : n=N := (query_ambient F a ha (payloadRows F width hm payloads) mark).symm.trans hN.symm
  cases hn
  dsimp only
  rw [factorSpec_sourceHashes]
  change PreparedBranchCount.fullCount
    (rawHashes (indexedSource F (formulaRecords_length F)) (payloadRows F width hm payloads))
    mark.isSome (F[(mark.map Fin.val).getD 0]?.getD [])=selectorCount F width payloads mark
  cases mark with
  | none => exact fullCount_formula_none F (formulaRecords_length F) width hm payloads _
  | some i =>
    simp only [Option.map_some,Option.getD_some,Option.isSome_some]
    rw [List.getElem?_eq_getElem (by simpa only [formulaRecords_length] using i.isLt),Option.getD_some]
    exact fullCount_formula_marked F (formulaRecords_length F) width hm payloads i

end
end SubexponentialSAT.SqrtLog.OuterQuery.Count

end OAI.Algorithms
