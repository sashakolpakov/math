import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowExecution
import OAI.Algorithms.SubexponentialSAT.SubexpRowSourceSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd

namespace OAI.Algorithms

/-!
# Typed dense literals for the emitted universal-row source

Each scalar payload is a one-coefficient dense polynomial. The variable
payload is the two-coefficient list `[zero, one]`. This file identifies the
actual emitted bytes with that typed expression, then identifies its source
polynomial meaning. No coefficient section is applied to the expression.
-/

namespace SubexponentialSAT.SubexpRowExpression

open SubexpSymbolicCost SubexpSelectedConversions


private theorem map_sum {A B : Type*} [Zero A] [Zero B] (f : A → B)
    (hzero : f 0 = 0) (es : List (Algorithm.Expr A)) :
    (Algorithm.Expr.sum es).map f = Algorithm.Expr.sum (es.map (Algorithm.Expr.map f)) := by
  induction es with
  | nil => simp only [List.map_nil, Algorithm.Expr.sum, Algorithm.Expr.map, hzero]
  | cons e es ih => simp only [Algorithm.Expr.sum, Algorithm.Expr.map, List.map_cons, ih]

private theorem map_product {A B : Type*} [One A] [One B] (f : A → B)
    (hone : f 1 = 1) (es : List (Algorithm.Expr A)) :
    (Algorithm.Expr.product es).map f =
      Algorithm.Expr.product (es.map (Algorithm.Expr.map f)) := by
  induction es with
  | nil => simp only [List.map_nil, Algorithm.Expr.product, Algorithm.Expr.map, hone]
  | cons e es ih => simp only [Algorithm.Expr.product, Algorithm.Expr.map, List.map_cons, ih]

private theorem map_factorExpression {A B : Type*} (f : A → B) (x : A) (r : Subexp.UniversalRowProgram.Factor A) :
    (Subexp.UniversalRowProgram.factorExpression x r).map f = Subexp.UniversalRowProgram.factorExpression (f x) (Subexp.UniversalRowProgram.mapFactor f r) := rfl

private theorem map_termExpression {A B : Type*} [One A] [One B] (f : A → B)
    (hone : f 1 = 1) (x : A) (r : Subexp.UniversalRowProgram.Term A) :
    (Subexp.UniversalRowProgram.termExpression x r).map f = Subexp.UniversalRowProgram.termExpression (f x) (Subexp.UniversalRowProgram.mapTerm f r) := by
  simp only [Subexp.UniversalRowProgram.termExpression, Algorithm.Expr.map, map_product f hone,
    Subexp.UniversalRowProgram.mapTerm, List.map_map, Function.comp_def, map_factorExpression]

private theorem map_rowExpression {A B : Type*} [Zero A] [One A] [Zero B] [One B]
    (f : A → B) (hzero : f 0 = 0) (hone : f 1 = 1) (x : A) (r : Subexp.UniversalRowProgram.Row A) :
    (Subexp.UniversalRowProgram.rowExpression x r).map f = Subexp.UniversalRowProgram.rowExpression (f x) (Subexp.UniversalRowProgram.mapRow f r) := by
  simp only [Subexp.UniversalRowProgram.rowExpression, Algorithm.Expr.map, map_sum f hzero,
    Subexp.UniversalRowProgram.mapRow, List.map_map, Function.comp_def, map_termExpression f hone]

private theorem mapRow_comp {A B C : Type*} (f : A → B) (g : B → C) (r : Subexp.UniversalRowProgram.Row A) :
    Subexp.UniversalRowProgram.mapRow g (Subexp.UniversalRowProgram.mapRow f r) = Subexp.UniversalRowProgram.mapRow (g ∘ f) r := by
  simp [Subexp.UniversalRowProgram.mapRow, Subexp.UniversalRowProgram.mapTerm, Subexp.UniversalRowProgram.mapFactor, List.map_map, Function.comp_def]

variable {p : ℕ} [Fact p.Prime] (source : Prepared p 0)

abbrev Coefficient (p : ℕ) := QuarticCode p 0

def encode (P : List (Coefficient p)) : List Bool :=
  (P.map SubexpFlatAdd.encode).flatten

omit [Fact p.Prime] in
@[simp] theorem encode_singleton (c : Coefficient p) :
    encode [c] = SubexpFlatAdd.encode c := by simp [encode]

omit [Fact p.Prime] in
@[simp] theorem encode_pair (a b : Coefficient p) :
    encode [a,b] = SubexpFlatAdd.encode a ++ SubexpFlatAdd.encode b := by simp [encode]

/-- Executable syntax: only scalar singleton literals, the literal X, and
the already-fixed universal-row sum/product structure occur here. -/
def expression (row : Subexp.UniversalRowProgram.Row (Coefficient p)) : Algorithm.Expr (List (Coefficient p)) :=
  letI : Zero (List (Coefficient p)) := ⟨[source.zero]⟩
  letI : One (List (Coefficient p)) := ⟨[source.one]⟩
  Subexp.UniversalRowProgram.rowExpression [source.zero,source.one] (Subexp.UniversalRowProgram.mapRow (fun c => [c]) row)

/-- The physical emitter's exact bytes are the compilation of the typed
dense-literal expression. This equality assumes no evaluator result. -/
theorem rowCode_eq_serialize (row : Subexp.UniversalRowProgram.Row (Coefficient p)) :
    Subexp.UniversalRowProgram.rowCode (SubexpFlatAdd.encode source.zero) (SubexpFlatAdd.encode source.one)
      (SubexpFlatAdd.encode source.zero ++ SubexpFlatAdd.encode source.one)
      (Subexp.UniversalRowProgram.mapRow SubexpFlatAdd.encode row) =
        SubexpPostfixControl.serializeCode encode (expression source row).compile := by
  let : Zero (List (Coefficient p)) := ⟨[source.zero]⟩
  let : One (List (Coefficient p)) := ⟨[source.one]⟩
  have h := Subexp.UniversalRowProgram.rowCode_eq encode [source.zero,source.one]
    (Subexp.UniversalRowProgram.mapRow (fun c => [c]) row)
  change Subexp.UniversalRowProgram.rowCode (encode [source.zero]) (encode [source.one])
      (encode [source.zero,source.one])
      (Subexp.UniversalRowProgram.mapRow encode (Subexp.UniversalRowProgram.mapRow (fun c => [c]) row)) =
    SubexpPostfixControl.serializeCode encode (expression source row).compile at h
  simpa only [mapRow_comp, Function.comp_def, encode_singleton, encode_pair] using h

@[simp] theorem denote_singleton (c : Coefficient p) :
    SubexpRowSourceSemantics.denote source [c] = Polynomial.C (source.residueRing.decode c) := by
  simp [SubexpRowSourceSemantics.denote]

@[simp] theorem denote_zero : SubexpRowSourceSemantics.denote source [source.zero] = 0 := by
  have h : source.residueRing.decode source.zero = 0 := source.residueRing.zero_correct
  simp [h]

@[simp] theorem denote_one : SubexpRowSourceSemantics.denote source [source.one] = 1 := by
  have h : source.residueRing.decode source.one = 1 := source.residueRing.one_correct
  simp [h]

@[simp] theorem denote_variable :
    SubexpRowSourceSemantics.denote source [source.zero,source.one] = Polynomial.X := by
  have hz : source.residueRing.decode source.zero = 0 := source.residueRing.zero_correct
  have ho : source.residueRing.decode source.one = 1 := source.residueRing.one_correct
  simp [SubexpRowSourceSemantics.denote, hz, ho]

/-- Decode the literals in the source field before any coefficient lift.
The result is exactly the polynomial row used by the cache/layout proof. -/
theorem expression_map (row : Subexp.UniversalRowProgram.Row (Coefficient p)) :
    (expression source row).map (SubexpRowSourceSemantics.denote source) =
      Subexp.UniversalRowProgram.rowExpression Polynomial.X
        (Subexp.UniversalRowProgram.mapRow (fun c => Polynomial.C (source.residueRing.decode c)) row) := by
  let : Zero (List (Coefficient p)) := ⟨[source.zero]⟩
  let : One (List (Coefficient p)) := ⟨[source.one]⟩
  have h := map_rowExpression (SubexpRowSourceSemantics.denote source)
    (denote_zero source) (denote_one source) [source.zero,source.one]
    (Subexp.UniversalRowProgram.mapRow (fun c => [c]) row)
  simpa only [expression, denote_variable, mapRow_comp, Function.comp_def, denote_singleton] using h

theorem expression_denote (row : Subexp.UniversalRowProgram.Row (Coefficient p)) :
    ((expression source row).map (SubexpRowSourceSemantics.denote source)).eval =
      (Subexp.UniversalRowProgram.rowExpression Polynomial.X
        (Subexp.UniversalRowProgram.mapRow (fun c => Polynomial.C (source.residueRing.decode c)) row)).eval :=
  congrArg Algorithm.Expr.eval (expression_map source row)

/-- The concrete source evaluator returns the complete row once its layout
degree bound has been established; intermediate degrees remain unrestricted. -/
theorem run_full_row (R : ℕ) (row : Subexp.UniversalRowProgram.Row (Coefficient p))
    (hdegree : (Subexp.UniversalRowProgram.rowExpression Polynomial.X
      (Subexp.UniversalRowProgram.mapRow (fun c => Polynomial.C (source.residueRing.decode c)) row)).eval.natDegree ≤ R) :
    SubexpRowSourceSemantics.denote source
        (SubexpRowSourceSemantics.run source (R + 1) (expression source row)) =
      (Subexp.UniversalRowProgram.rowExpression Polynomial.X
        (Subexp.UniversalRowProgram.mapRow (fun c => Polynomial.C (source.residueRing.decode c)) row)).eval := by
  have hd : ((expression source row).map (SubexpRowSourceSemantics.denote source)).eval.natDegree <
      R + 1 := by
    rw [expression_denote]
    exact Nat.lt_succ_of_le hdegree
  rw [SubexpRowSourceSemantics.run_full_row source (R + 1) (expression source row) hd,
    expression_denote]

end SubexponentialSAT.SubexpRowExpression

end OAI.Algorithms
