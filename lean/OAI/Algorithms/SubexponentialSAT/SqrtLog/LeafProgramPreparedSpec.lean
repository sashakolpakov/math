import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSource

namespace OAI.Algorithms

/-! A typed factor specification using the original query's row stream and
marked-clause selector. Finite-index transports do not alter stored bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics MomentsProgram
noncomputable section

def castRows {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    HashScopeProgram.RawTable.Rows m' :=
  rows.map (List.map (fun a => (Fin.cast h a.1,a.2)))

@[simp] theorem castRows_length {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) :
    (castRows h rows).length=rows.length := by simp [castRows]

theorem castRows_bytes {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) (b : ℕ) :
    HashScopeProgram.RawTable.inputBits b (castRows h rows)=HashScopeProgram.RawTable.inputBits b rows := by
  subst m'
  simp [castRows]

theorem origin_good {r Q n d : ℕ} (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    Good Finset.univ u J (NodeNative.originEntries (n:=n) p.ops.oneRun.1) :=
  FactorBounds.indicator_good_iff.mp (NodeNative.originEntries_valid _ _ u J hu hJ)

theorem origin_value {r Q n d : ℕ} (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    rawDenote p.ops.decode (NodeNative.originEntries (n:=n) p.ops.oneRun.1)=Squarefree.canonical u J 1 := by
  have h := Squarefree.Sparse.denote_one (V:=Fin n) (R:=p.model.O p.t) u J
  simpa only [Squarefree.Sparse.one,Squarefree.Sparse.constant,hu,hJ,and_self,ite_true,
    rawDenote,NodeNative.originEntries,Dictionary.denoteTable,List.map_cons,List.map_nil,p.ops.one_correct] using h

def markIndex (q : LeafQueryFrontend.Query) : ℕ := (q.mark.map Fin.val).getD 0

theorem markIndex_valid (q : LeafQueryFrontend.Query) :
    q.mark.isSome=true → markIndex q < q.clauses.length := by
  cases h : q.mark with
  | none => simp
  | some v => simp [markIndex,h,v.isLt]

def factorSpec {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : ConstructivePacking.PackingData (Fin ps.length) (UniversalType r Q 1))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin n)))) (hc : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) : Factor.Spec r Q n d where
  p := p
  ps := ps
  packing := P
  u := p.t
  J := J
  hu := p.ht
  hJ := hJ
  theta := theta
  width := width
  widthLength := hw
  minus := p.minusOne
  minusValue := p.hminus
  one := NodeNative.originEntries p.ops.oneRun.1
  oneGood := origin_good p p.t J p.ht hJ
  oneValue := origin_value p p.t J p.ht hJ
  source := source
  rows := castRows (congrArg List.length hc) q.rows
  bitWidth := q.width.length
  bitWidthPositive := hv.1
  sourceBound := by simpa only [hc] using hv.2.2.2.1
  code := code
  marked := q.mark.isSome
  mark := markIndex q
  markValid := by
    have h := markIndex_valid q
    simpa only [hc,HashInputProgram.Expansion.encodedClauses,List.length_map] using h

theorem factorSpec_row_bytes {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : ConstructivePacking.PackingData (Fin ps.length) (UniversalType r Q 1))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin n)))) (hc : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    Encoding.encodeList id (factorSpec p ps P q hv J hJ source hc theta width hw code).rawRows=
      HashScopeProgram.RawTable.inputBits q.width.length q.rows := by
  change Encoding.encodeList id ((castRows (congrArg List.length hc) q.rows).map
    (fun ts => (HashInputProgram.Loop.rawInput q.width.length ts).reverse))=_
  simp only [HashInputProgram.Loop.rawInput,List.reverse_reverse]
  exact castRows_bytes _ _ _

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
