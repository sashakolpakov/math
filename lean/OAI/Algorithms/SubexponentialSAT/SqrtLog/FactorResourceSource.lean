import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

/-! A fixed polynomial for the actual native source service. Its arguments
are the physical source-word bounds, never a supplied execution cost. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT Subexp SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram CostAssembly.Polynomial

def mismatchEnvelope (r Q : ℕ) : ℕ :=
  9*Q+13+(Q*(12*Q+23)+2)+8+
    Q*(6*Q+((28*r+39)*Q+43*r+80)+7)+10*(1+(2*Q+2)*Q)

theorem mismatch_le (r Q : ℕ) :
    UniversalRowMismatchProgram.budget Q r ≤ mismatchEnvelope r Q := by
  let xs := MismatchPlanProgram.indexRecords (List.range Q).reverse
  have hl : xs.length=Q := by simp [xs,MismatchPlanProgram.indexRecords]
  have hx : ∀ x ∈ xs,x.length ≤ Q := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    simpa using (List.mem_range.mp (List.mem_reverse.mp hi)).le
  have hc : ∀ x ∈ xs,MismatchPlanProgram.callbackCost r x ≤ (28*r+39)*Q+43*r+80 := by
    intro x hx'
    unfold MismatchPlanProgram.callbackCost
    gcongr
    exact hx x hx'
  have hb := UniversalRowSourceBound.record_budget_le (MismatchPlanProgram.callbackCost r)
    xs Q ((28*r+39)*Q+43*r+80) hx hc
  have he := Encoding.length_encodeList_upper id xs Q hx
  have hu := SubexpUnaryRangeProgram.steps_le 0 Q
  rw [hl] at hb he
  simp only [Nat.zero_add] at hu
  unfold UniversalRowMismatchProgram.budget MismatchPlanProgram.sourceBound mismatchEnvelope
  dsimp only [xs] at hb he
  omega

def integerLiftEnvelope (bits d w : ℕ) : ℕ :=
  bits*(100000*(d+1)^3*(w+1)^2+80*d*w+110)+
    200000*(d+1)^3*(w+1)^2+203*d*w+251

def tableEnvelope (r Q A R W P d w : ℕ) : ℕ :=
  let bits := LayoutSourceValuesProgram.Native.integerBits R W P
  Q*(Q*LayoutSourceValuesProgram.Native.numeratorAllowance r Q A R W P+
    1+integerLiftEnvelope bits d w+2*bits+6+6*(d*w)+16)+14

def bankEnvelope (r Q A R W P d w S : ℕ) : ℕ :=
  let workspace := S+Q*(d*w)+UniversalRowSourceBound.indicesBound Q
  tableEnvelope r Q A R W P d w+
    (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
      mismatchEnvelope r Q+8*(Q*r)+13)+
    14*S+224*workspace+UniversalRowSourceBound.sourceBound workspace+281

def sourceEnvelope (X : ℕ) : ℕ :=
  let source := 800*(2*X+1)^2+bankEnvelope X X X X X X X X X+200*X+302+12*X+12
  let W := (X+1)*(X*X)
  LayoutSourceRowsProgramInitialize.budget (X+1) (X*X)+1000*(4*X+1)^2+
    X*(rowBudgetPolynomial source (UniversalRowSourceBound.sourceLengthBound X)
      (X+1) X X X+45*W+83)+2*X+23+
    1000000000000*(X+(67108864*X+1+W+(X+1)+X*(2*W+2)+1)+1)

structure SourceCaps {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S X : ℕ) : Prop where
  source : S ≤ X
  colors : r ≤ X
  nodes : Q ≤ X
  offset : p.aWord.length ≤ X
  radius : p.R ≤ X
  scalarWidth : p.width.length ≤ X
  power : RowSelectionProgram.pairLength p.power ≤ X
  dimension : d ≤ X
  width : baseWidth 3 p.t ≤ X

theorem nativeSource_le {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S X : ℕ)
    (h : SourceCaps p S X) : Source.nativeSourceWorkPolynomial p S ≤ sourceEnvelope X := by
  have hm := mismatch_le r Q
  have ht : SourceBank.uniformBudget p S ≤ bankEnvelope r Q p.aWord.length p.R p.width.length
      (RowSelectionProgram.pairLength p.power) d (baseWidth 3 p.t) S := by
    unfold SourceBank.uniformBudget bankEnvelope tableEnvelope SourceBank.sourceWorkspace
    unfold LayoutSourceValuesProgram.Native.polynomialBudget LayoutSourceValuesProgram.Native.callbackBudget
      IntegerRingLiftProgram.polynomialBudget integerLiftEnvelope
    dsimp only
    omega
  have hb : bankEnvelope r Q p.aWord.length p.R p.width.length
      (RowSelectionProgram.pairLength p.power) d (baseWidth 3 p.t) S ≤ bankEnvelope X X X X X X X X X := by
    dsimp only [bankEnvelope,tableEnvelope,integerLiftEnvelope,
      LayoutSourceValuesProgram.Native.integerBits,LayoutProgramScalar.termGrowth,
      LayoutSourceValuesProgram.Native.numeratorAllowance,LayoutSourceValuesProgram.Native.scalarAllowance,
      MatrixExtendedEntryProgram.guardStageCost,MatrixEntryProgram.scanStageCost,CollisionProgram.typeWidth,
      LayoutProgramScalar.FromCounts.binomialCost,LayoutProgramScalar.numeratorPrepareCost,
      LayoutProgramScalar.numeratorFoldCost,UniversalRowMismatchTypes.extractBudget,mismatchEnvelope,
      UniversalRowSourceBound.indicesBound,UniversalRowSourceBound.sourceBound,
      UniversalRowSourceBound.dataBound,UniversalRowSourceBound.outerLoopBound,
      UniversalRowSourceBound.termBound,UniversalRowSourceBound.factorLoopBound,
      UniversalRowSourceBound.factorCallbackBound,UniversalRowSourceBound.inputBound,
      UniversalRowSourceBound.rowBytes,UniversalRowSourceBound.termBytes,
      UniversalRowSourceBound.factorsBytes,UniversalRowSourceBound.factorBytes]
    gcongr <;> first | exact h.source | exact h.colors | exact h.nodes | exact h.offset |
      exact h.radius | exact h.scalarWidth | exact h.power | exact h.dimension | exact h.width
  have hs := ht.trans hb
  have hlen := LayoutSourceExpression.sourceLengthBound_mono h.source
  dsimp only [Source.nativeSourceWorkPolynomial,nativeRowsPolynomial,stagedSourceBudget,
    nativeSourceBudget,Source.nativeOutputBound,sourceEnvelope,
    LayoutSourceRowsProgramInitialize.budget,rowBudgetPolynomial]
  gcongr <;> first | exact hs | exact hlen | exact h.source | exact h.colors | exact h.nodes |
    exact h.offset | exact h.radius | exact h.scalarWidth | exact h.power | exact h.dimension | exact h.width

theorem sourceEnvelope_diagonal (X : ℕ) : sourceEnvelope X =
      524288*X^20 +
      6291456*X^19 +
      40894464*X^18 +
      182714368*X^17 +
      23658659840*X^16 +
      312706973696*X^15 +
      1905917650972*X^14 +
      7009475713248*X^13 +
      17406351890416*X^12 +
      30996636364003*X^11 +
      41021925077242*X^10 +
      41562424812031*X^9 +
      33026180618882*X^8 +
      20359973829153*X^7 +
      9172114950978*X^6 +
      2876283754348*X^5 +
      2649156148766*X^4 +
      3094185613036*X^3 +
      1006536966561*X^2 +
      67108868000007209398*X +
      4000000001503 := by
  dsimp only [sourceEnvelope,bankEnvelope,tableEnvelope,integerLiftEnvelope,
    LayoutSourceValuesProgram.Native.integerBits,LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance,LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost,MatrixEntryProgram.scanStageCost,CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost,LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost,UniversalRowMismatchTypes.extractBudget,mismatchEnvelope,
    UniversalRowSourceBound.indicesBound,UniversalRowSourceBound.sourceBound,
    UniversalRowSourceBound.sourceLengthBound,UniversalRowSourceBound.dataBound,
    UniversalRowSourceBound.outerLoopBound,UniversalRowSourceBound.termBound,
    UniversalRowSourceBound.factorLoopBound,UniversalRowSourceBound.factorCallbackBound,
    UniversalRowSourceBound.inputBound,UniversalRowSourceBound.rowBytes,UniversalRowSourceBound.termBytes,
    UniversalRowSourceBound.factorsBytes,UniversalRowSourceBound.factorBytes,
    LayoutSourceRowsProgramInitialize.budget,rowBudgetPolynomial]
  norm_num only [Fin.val_zero]
  ring

theorem sourceEnvelope_polynomial : Ordinary sourceEnvelope := by
  refine ⟨67109084423766658649,20,?_⟩
  intro X
  have hp (j : ℕ) (hj : j ≤ 20) : X^j ≤ (X+1)^20 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^20 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^20 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  have h10 := hp 10 (by decide)
  have h11 := hp 11 (by decide)
  have h12 := hp 12 (by decide)
  have h13 := hp 13 (by decide)
  have h14 := hp 14 (by decide)
  have h15 := hp 15 (by decide)
  have h16 := hp 16 (by decide)
  have h17 := hp 17 (by decide)
  have h18 := hp 18 (by decide)
  have h19 := hp 19 (by decide)
  have h20 := hp 20 (by decide)
  rw [sourceEnvelope_diagonal]
  omega

/-- Constants are chosen before every source parameter or input word. -/
theorem nativeSource_polynomial : ∃ C e : ℕ, ∀ {r Q d : ℕ}
    (p : SourceBank.Parameters r Q d) (S X : ℕ), SourceCaps p S X →
    Source.nativeSourceWorkPolynomial p S ≤ C*(X+1)^e := by
  obtain ⟨C,e,h⟩ := sourceEnvelope_polynomial
  exact ⟨C,e,fun p S X hc => (nativeSource_le p S X hc).trans (h X)⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
