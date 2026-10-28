import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceTyped

namespace OAI.Algorithms

/-! Degree certificates for the actual typed literal and interpolation-row
sources. These remove the full-polynomial cutoff premise at R+1. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

/-- A native scalar literal is exactly one typed coefficient cell. -/
theorem literal_code {B d : ℕ} (c : Coeff B d) :
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode
      (Algorithm.Expr.lit [c]).compile = SubexpKernelControl.pushWord (RingProgram.flat c) := by
  simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr,DensePolynomialProgram.encode,SubexpKernelControl.pushWord]

theorem literal_meaning {C O : Type*} [CommRing O] (ops : RepresentedRing C O) (c : C) :
    ((Algorithm.Expr.lit [c]).map (meaning ops)).eval = Polynomial.C (ops.decode c) := by
  simp [Algorithm.Expr.map,Algorithm.Expr.eval,meaning,PolynomialAlgorithm.denote]

theorem literal_natDegree {C O : Type*} [CommRing O] (ops : RepresentedRing C O) (c : C) :
    (((Algorithm.Expr.lit [c]).map (meaning ops)).eval).natDegree = 0 := by
  rw [literal_meaning]
  simp

theorem literal_zero_meaning {C O : Type*} [CommRing O] (ops : RepresentedRing C O) :
    ((Algorithm.Expr.lit [ops.zeroRun.1]).map (meaning ops)).eval = 0 := by
  rw [literal_meaning,ops.zero_correct]
  simp

theorem literal_one_meaning {C O : Type*} [CommRing O] (ops : RepresentedRing C O) :
    ((Algorithm.Expr.lit [ops.oneRun.1]).map (meaning ops)).eval = 1 := by
  rw [literal_meaning,ops.one_correct]
  simp

/-- The full cutoff is discharged even for the actual zero and one literals. -/
theorem literal_evaluate_full {C O : Type*} [CommRing O]
    (ops : RepresentedRing C O) (c : C) (R : ℕ) :
    meaning ops (evaluate ops.program (R+1) (Algorithm.Expr.lit [c])) =
      Polynomial.C (ops.decode c) := by
  rw [evaluate_full ops (R+1) _ (by rw [literal_natDegree]; omega),literal_meaning]

/-- Any exact source-row witness inherits the audited full source degree. -/
theorem source_row_degree {C O : Type*} [CommRing O] {r Q Δ : ℕ}
    (ops : RepresentedRing C O) (row : Row C)
    (N : LayoutScaledMatrices.Numerators r Q Δ) (denom : Oˣ)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) {node : Fin Q → O}
    (units : NodeUnits node) (y : UniversalType r Q Δ)
    (hm : (rowExpression Polynomial.X
      (mapRow (fun c => Polynomial.C (ops.decode c)) row)).eval =
        LayoutScaledMatrices.sourceRow N denom u i R units y) :
    (((sourceExpr ops.program row).map (meaning ops)).eval).natDegree ≤ R := by
  rw [sourceExpr_meaning,hm]
  exact LayoutScaledMatrices.sourceRow_degree N denom u i R units y

/-- No separate degree assumption remains at the source's R+1 cutoff. -/
theorem source_row_evaluate_full {C O : Type*} [CommRing O] {r Q Δ : ℕ}
    (ops : RepresentedRing C O) (row : Row C)
    (N : LayoutScaledMatrices.Numerators r Q Δ) (denom : Oˣ)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) {node : Fin Q → O}
    (units : NodeUnits node) (y : UniversalType r Q Δ)
    (hm : (rowExpression Polynomial.X
      (mapRow (fun c => Polynomial.C (ops.decode c)) row)).eval =
        LayoutScaledMatrices.sourceRow N denom u i R units y) :
    meaning ops (evaluate ops.program (R+1) (sourceExpr ops.program row)) =
      LayoutScaledMatrices.sourceRow N denom u i R units y := by
  rw [evaluate_full ops (R+1) _ (Nat.lt_succ_of_le
    (source_row_degree ops row N denom u i R units y hm)),sourceExpr_meaning,hm]

section TypedRows

variable {C O : Type*} [Nonempty C] [CommRing O] {r Q : ℕ}
    (encode : C → List Bool) (tables : SubexponentialSAT.Subexp.UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (hvalues : ∀ i, tables.values.getD i.val []=encode (values i))
    (hinverse : ∀ i, tables.inverses.getD i.val []=encode (inverse i))
    (hnegative : ∀ i, tables.negatives.getD i.val []=encode (negative i))
    (hdifference : ∀ i j, (tables.differences.getD i.val []).getD j.val []=encode (difference i j))
    (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

include hvalues hinverse hnegative hdifference hinteger hinvDenom hnode hnodeInverse hdiffInverse in
/-- Concrete native table values give a typed expression of degree at most R,
and evaluation at R+1 recovers the complete source polynomial. The degree
conclusion is derived here, not supplied by the caller. -/
theorem typed_row_contract (hi : Function.Injective encode)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
    (hlimit : limit.length=R)
    (hv : ∀ i,ops.decode (values i)=ops.decode
      (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
    let row := LayoutProgram.SourceTyped.row values inverse negative difference
      (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
    let e := sourceExpr ops.program row
    ((e.map (meaning ops)).eval =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) ∧
    (((e.map (meaning ops)).eval).natDegree ≤ R) ∧
    (meaning ops (evaluate ops.program (R+1) e) =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) := by
  intro row e
  have hm := LayoutProgram.SourceTyped.row_meaning
    (encode := encode) (tables := tables) (values := values) (inverse := inverse)
    (negative := negative) (difference := difference)
    (hvalues := hvalues) (hinverse := hinverse) (hnegative := hnegative) (hdifference := hdifference)
    (ops := ops) (cache := cache) (integerWord := integerWord) (hinteger := hinteger)
    (denom := denom) (invDenom := invDenom) (hinvDenom := hinvDenom)
    (units := units) (hnode := hnode) (hnodeInverse := hnodeInverse) (hdiffInverse := hdiffInverse)
    hi A R u y delta limit hlimit hv hiv hnv hdv hdelta
  refine ⟨?_,source_row_degree ops row _ denom u 0 R units y hm,
    source_row_evaluate_full ops row _ denom u 0 R units y hm⟩
  rw [sourceExpr_meaning]
  exact hm

end TypedRows
end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
