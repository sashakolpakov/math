import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression

namespace OAI.Algorithms

/-! A complete typed witness for one actual universal source word: compiler
bytes, full polynomial meaning, degree, and physical byte length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness
open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

variable {B d r Q : ℕ} {O : Type*} [CommRing O]

def Generated (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (value : Polynomial O) (bytes : List Bool) : Prop :=
  ∃ e : Algorithm.Expr (List (Coeff B d)),
    bytes=SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile ∧
    (e.map (meaning ops)).eval=value ∧
    ((e.map (meaning ops)).eval).natDegree ≤ R ∧ bytes.length ≤ L

theorem literal (ops : RepresentedRing (Coeff B d) O) (R L : ℕ) (c : Coeff B d)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ L) :
    Generated ops R L (Polynomial.C (ops.decode c))
      (SubexpKernelControl.pushWord (RingProgram.flat c)) := by
  refine ⟨.lit [c],(LayoutSourceExpression.literal_code c).symm,
    LayoutSourceExpression.literal_meaning ops c,?_,hlen⟩
  rw [LayoutSourceExpression.literal_natDegree]
  exact Nat.zero_le _

theorem literal_zero (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat ops.zeroRun.1)).length ≤ L) :
    Generated ops R L 0 (SubexpKernelControl.pushWord (RingProgram.flat ops.zeroRun.1)) := by
  simpa only [ops.zero_correct,Polynomial.C_0] using literal ops R L ops.zeroRun.1 hlen

theorem literal_one (ops : RepresentedRing (Coeff B d) O) (R L : ℕ)
    (hlen : (SubexpKernelControl.pushWord (RingProgram.flat ops.oneRun.1)).length ≤ L) :
    Generated ops R L 1 (SubexpKernelControl.pushWord (RingProgram.flat ops.oneRun.1)) := by
  simpa only [ops.one_correct,Polynomial.C_1] using literal ops R L ops.oneRun.1 hlen

theorem universal (ops : RepresentedRing (Coeff B d) O) (hB : 0 < B)
    (cache : NodeCache (Coeff B d) Q)
    (integerWord : ℤ → Coeff B d) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : Coeff B d) (hinv : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hni : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdi : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)
    (values inverse negative : Fin Q → Coeff B d) (difference : Fin Q → Fin Q → Coeff B d)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : Coeff B d) (limit : List Bool)
    (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hi : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hn : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdiff : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length=R)
    (width rowWidth : List Bool) (hw : width.length=d*B) (hrw : rowWidth.length=Q*width.length)
    (S : ℕ) (hQ : Q ≤ S) (hW : width.length ≤ S) (hRW : rowWidth.length ≤ S) (hR : R ≤ S) :
    Generated ops R (UniversalRowSourceBound.sourceLengthBound S)
      (LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y)
      (UniversalRowProgram.rowCode (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1)
        (RingProgram.flat ops.zeroRun.1++RingProgram.flat ops.oneRun.1)
        (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat values inverse negative difference)
          (UniversalRowTableSource.positions (mismatchPositions (fun v=>v.head) (u.slot 0) y))
          (RingProgram.flat delta) limit)) := by
  let : Nonempty (Coeff B d) := ⟨ops.zeroRun.1⟩
  let ts := SourceTyped.tables RingProgram.flat values inverse negative difference
  let s := mismatchPositions (fun v=>v.head) (u.slot 0) y
  let row := SourceTyped.row values inverse negative difference s delta R
  let e := sourceExpr ops.program row
  have hc := SourceTyped.code_witness ops.program ts values inverse negative difference
    (SourceTyped.tables_values _ _ _ _ _) (SourceTyped.tables_inverse _ _ _ _ _)
    (SourceTyped.tables_negative _ _ _ _ _) (SourceTyped.tables_difference _ _ _ _ _) s delta limit
  have hm := LayoutSourceExpression.typed_row_contract
    RingProgram.flat ts values inverse negative difference
    (SourceTyped.tables_values _ _ _ _ _) (SourceTyped.tables_inverse _ _ _ _ _)
    (SourceTyped.tables_negative _ _ _ _ _) (SourceTyped.tables_difference _ _ _ _ _)
    ops cache integerWord hinteger denom invDenom hinv units hnode hni hdi
    (RingProgram.flat_injective hB) A R u y delta limit hlimit hv hi hn hdiff hdelta
  have hlen (c : Coeff B d) : (RingProgram.flat c).length=width.length :=
    (RingProgram.flat_length c).trans hw.symm
  have hb := SourceTyped.source_bounds RingProgram.flat values inverse negative difference
    width rowWidth hlen hrw s (RingProgram.flat delta) limit
    (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1) S hQ hW hRW
    (by rw [hlen]; exact hW) (by rw [hlimit]; exact hR)
    (by rw [hlen]; exact hW) (by rw [hlen]; exact hW)
  refine ⟨e,?_,hm.1,hm.2.1,hb.2⟩
  simpa only [hlimit] using hc

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness

end OAI.Algorithms
