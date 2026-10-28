import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramSource

namespace OAI.Algorithms

/-! Typed witnesses for the actual interpolation table reads. Cached negative
nodes and inverse differences need only have the right decoded value; no
canonical representation or equality with an arithmetic implementation is
assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowProgram SubexponentialSAT.Subexp.UniversalRowSource
open SubexponentialSAT.Subexp.UniversalRowTableSource SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation

variable {C O : Type*} {Q : ℕ}

def factor (negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (i j : Fin Q) : Factor C := ⟨difference i j,negative j⟩

def term (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (s : Finset (Fin Q)) (i : Fin Q) : Term C :=
  ⟨values i,inverse i,(selected (s.erase i)).map (factor negative difference i)⟩

def row (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (s : Finset (Fin Q)) (delta : C) (R : ℕ) : Row C :=
  ⟨delta,if s.card ≤ R then (selected s).map (term values inverse negative difference s) else []⟩

variable (encode : C → List Bool) (tables : UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (hvalues : ∀ i, tables.values.getD i.val []=encode (values i))
    (hinverse : ∀ i, tables.inverses.getD i.val []=encode (inverse i))
    (hnegative : ∀ i, tables.negatives.getD i.val []=encode (negative i))
    (hdifference : ∀ i j, (tables.differences.getD i.val []).getD j.val []=encode (difference i j))

include hnegative hdifference in
theorem factors_eq (s : Finset (Fin Q)) (i : Fin Q) :
    UniversalRowFactorLoop.factors (tables.differences.getD i.val []) tables.negatives i.val (positions s)=
      (selected (s.erase i)).map (fun j => UniversalRowSource.mapFactor encode (factor negative difference i j)) := by
  unfold UniversalRowFactorLoop.factors
  rw [positions_filter,positions,List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_def,UniversalRowFactorLoop.factor,hdifference,hnegative,UniversalRowSource.mapFactor,factor]

include hvalues hinverse hnegative hdifference in
theorem term_eq (s : Finset (Fin Q)) (i : Fin Q) :
    UniversalRowLoop.term tables (positions s) i.val=
      UniversalRowSource.mapTerm encode (term values inverse negative difference s i) := by
  simp only [UniversalRowLoop.term,UniversalRowTermProgram.term,UniversalRowSource.mapTerm,term,List.map_map]
  rw [hvalues,hinverse,factors_eq encode tables negative difference hnegative hdifference]
  rfl

include hvalues hinverse hnegative hdifference in
/-- The actual raw row record is the encoding of a concrete typed row. -/
theorem row_eq (s : Finset (Fin Q)) (delta : C) (limit : List Bool) :
    UniversalRowDataProgram.row tables (positions s) (encode delta) limit=
      UniversalRowSource.mapRow encode (row values inverse negative difference s delta limit.length) := by
  simp only [UniversalRowDataProgram.row,row,UniversalRowSource.mapRow,positions_length]
  by_cases h : s.card ≤ limit.length
  · simp only [ite_eq_left h,positions,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    exact term_eq encode tables values inverse negative difference hvalues hinverse hnegative hdifference s i
  · simp [h]

/-- A left inverse is used only to state decoding of raw literals. It is not
executed by the polynomial source program. -/
noncomputable def wordDecode [Nonempty C] (encode : C → List Bool) (decode : C → O) : List Bool → O :=
  fun w => decode (Function.invFun encode w)

theorem wordDecode_encode [Nonempty C] (encode : C → List Bool) (hi : Function.Injective encode)
    (decode : C → O) (c : C) : wordDecode encode decode (encode c)=decode c := by
  rw [wordDecode,Function.leftInverse_invFun hi c]

variable [CommRing O] (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

include hvalues hinverse hnegative hdifference hinteger hinvDenom hnode hnodeInverse hdiffInverse in
/-- Arbitrary valid native coefficient representations give the exact source
row over O, with full degree at most R. -/
theorem row_meaning [Nonempty C] {r : ℕ} (hi : Function.Injective encode)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
    (hlimit : limit.length=R)
    (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
    let typed := row values inverse negative difference (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
    (rowExpression Polynomial.X (UniversalRowSource.mapRow (fun c => Polynomial.C (ops.decode c)) typed)).eval=
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y := by
  intro typed
  let decode := wordDecode encode ops.decode
  have hdecode : ∀ c,decode (encode c)=ops.decode c := wordDecode_encode encode hi ops.decode
  have h := LayoutProgram.tableSource_eq ops cache integerWord hinteger denom invDenom hinvDenom
    units hnode hnodeInverse hdiffInverse decode tables A R u y (0:Fin 1) (encode delta) limit
    (fun i => by rw [hvalues,hdecode,hv])
    (fun i => by rw [hinverse,hdecode,hiv])
    (fun i j => by rw [hdifference,hdecode,hdv])
    (fun i => by rw [hnegative,hdecode,hnv])
    (by rw [hdecode,hdelta]) hlimit
  rw [row_eq encode tables values inverse negative difference hvalues hinverse hnegative hdifference,
    hlimit,UniversalRowTableSource.mapRow_comp] at h
  have hfun : (fun bits => Polynomial.C (decode bits)) ∘ encode=
      fun c => Polynomial.C (ops.decode c) := by funext c; simp [hdecode]
  rw [hfun] at h
  exact h

/-- The generated bytes are precisely a typed postfix compiler output,
not merely a string with the desired denotation. -/
theorem code_witness {B d Q : ℕ}
    (ops : RingProgram (PolynomialExecutorProgram.Coeff B d))
    (tables : UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → PolynomialExecutorProgram.Coeff B d)
    (difference : Fin Q → Fin Q → PolynomialExecutorProgram.Coeff B d)
    (hvalues : ∀ i,tables.values.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (values i))
    (hinverse : ∀ i,tables.inverses.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (inverse i))
    (hnegative : ∀ i,tables.negatives.getD i.val []=SubexponentialSAT.SqrtLog.RingProgram.flat (negative i))
    (hdifference : ∀ i j,(tables.differences.getD i.val []).getD j.val []=
      SubexponentialSAT.SqrtLog.RingProgram.flat (difference i j))
    (s : Finset (Fin Q)) (delta : PolynomialExecutorProgram.Coeff B d) (limit : List Bool) :
    rowCode (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1++SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (UniversalRowDataProgram.row tables (positions s) (SubexponentialSAT.SqrtLog.RingProgram.flat delta) limit)=
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode
      (PolynomialExecutorProgram.sourceExpr ops
        (row values inverse negative difference s delta limit.length)).compile := by
  rw [row_eq SubexponentialSAT.SqrtLog.RingProgram.flat tables values inverse negative difference
    hvalues hinverse hnegative hdifference]
  exact PolynomialExecutorProgram.sourceCode_eq ops _

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
