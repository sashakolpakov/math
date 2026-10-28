import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramBasic
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowExecution

namespace OAI.Algorithms

/-! The physical row-source emitter's bytes are exactly the input accepted by
the generic coefficient-array interpreter. Scalar literals are single cells;
the formal variable has the two-cell representation [zero, one]. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram

private theorem map_product {A B : Type*} [One A] [One B]
    (f : A → B) (h1 : f 1 = 1) (es : List (Algorithm.Expr A)) :
    (Algorithm.Expr.product es).map f = Algorithm.Expr.product (es.map (Algorithm.Expr.map f)) := by
  induction es with
  | nil => simp [Algorithm.Expr.product,Algorithm.Expr.map,h1]
  | cons e es ih => simp [Algorithm.Expr.product,Algorithm.Expr.map,ih]

theorem map_rowExpression {A B : Type*} [Zero A] [One A] [Zero B] [One B]
    (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) (x : A) (r : Row A) :
    (rowExpression x r).map f = rowExpression (f x) (mapRow f r) := by
  simp [rowExpression,Algorithm.Expr.map,Algorithm.Expr.map_sum f h0,
    map_product f h1,List.map_map,Function.comp_def,termExpression,factorExpression,
    mapRow,mapTerm,mapFactor]

def sourceExpr {C : Type*} (ops : RingProgram C) (r : Row C) : Algorithm.Expr (List C) :=
  letI : Zero (List C) := ⟨[ops.zeroRun.1]⟩
  letI : One (List C) := ⟨[ops.oneRun.1]⟩
  rowExpression [ops.zeroRun.1,ops.oneRun.1] (mapRow (fun c => [c]) r)

theorem sourceCode_eq {B d : ℕ} (ops : RingProgram (Coeff B d)) (r : Row (Coeff B d)) :
    rowCode (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (SubexponentialSAT.SqrtLog.RingProgram.flat ops.zeroRun.1 ++ SubexponentialSAT.SqrtLog.RingProgram.flat ops.oneRun.1)
      (mapRow SubexponentialSAT.SqrtLog.RingProgram.flat r) =
    SubexpPostfixControl.serializeCode DensePolynomialProgram.encode (sourceExpr ops r).compile := by
  let _ : Zero (List (Coeff B d)) := ⟨[ops.zeroRun.1]⟩
  let _ : One (List (Coeff B d)) := ⟨[ops.oneRun.1]⟩
  have hzero : (0 : List (Coeff B d)) = [ops.zeroRun.1] := rfl
  have hone : (1 : List (Coeff B d)) = [ops.oneRun.1] := rfl
  have h := rowCode_eq DensePolynomialProgram.encode [ops.zeroRun.1,ops.oneRun.1]
    (mapRow (fun c => [c]) r)
  have hmap : mapRow DensePolynomialProgram.encode (mapRow (fun c => [c]) r) =
      mapRow SubexponentialSAT.SqrtLog.RingProgram.flat r := by
    cases r
    simp [mapRow, mapTerm, mapFactor, DensePolynomialProgram.encode,
      List.map_map, Function.comp_def]
  rw [hmap] at h
  simpa [hzero, hone, sourceExpr, DensePolynomialProgram.encode] using h

theorem sourceExpr_meaning {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (r : Row C) :
    (sourceExpr ops.program r).map (meaning ops) =
      rowExpression Polynomial.X (mapRow (fun c => Polynomial.C (ops.decode c)) r) := by
  let _ : Zero (List C) := ⟨[ops.zeroRun.1]⟩
  let _ : One (List C) := ⟨[ops.oneRun.1]⟩
  have h0 : meaning ops (0 : List C) = 0 := by
    change meaning ops [ops.zeroRun.1] = 0
    simp [meaning,PolynomialAlgorithm.denote,ops.zero_correct]
  have h1 : meaning ops (1 : List C) = 1 := by
    change meaning ops [ops.oneRun.1] = 1
    simp [meaning,PolynomialAlgorithm.denote,ops.one_correct]
  have h := map_rowExpression (meaning ops) h0 h1 [ops.zeroRun.1,ops.oneRun.1]
    (mapRow (fun c => [c]) r)
  have hc (c : C) : meaning ops [c] = Polynomial.C (ops.decode c) := by
    simp [meaning, PolynomialAlgorithm.denote]
  have hmap : mapRow (meaning ops) (mapRow (fun c => [c]) r) =
      mapRow (fun c => Polynomial.C (ops.decode c)) r := by
    cases r
    simp [mapRow, mapTerm, mapFactor, List.map_map, Function.comp_def, hc]
  rw [hmap] at h
  have hx : meaning ops [ops.zeroRun.1, ops.oneRun.1] = Polynomial.X := by
    simp [meaning, PolynomialAlgorithm.denote, ops.zero_correct, ops.one_correct]
  rw [hx] at h
  simpa [sourceExpr] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
