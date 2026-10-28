import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows

namespace OAI.Algorithms

/-!
# Filtered row records for the physical interpolation-code emitter

Inactive zero terms and unit factors are omitted from the emitted records.
This is proved as a polynomial identity, without identifying the two different
expression trees or assuming a desired evaluator result.
-/

namespace SubexponentialSAT.Subexp.UniversalRowSource

open scoped BigOperators
open SubexpSymbolicCost SubexpRowInterpolation SubexpRepresentedRows
open UniversalRowProgram

variable {C E : Type*} {Q : ℕ}

def selected (s : Finset (Fin Q)) : List (Fin Q) :=
  (List.finRange Q).filter fun i => decide (i ∈ s)

@[simp] theorem selected_toFinset (s : Finset (Fin Q)) : (selected s).toFinset = s := by
  ext i
  simp [selected]

theorem selected_nodup (s : Finset (Fin Q)) : (selected s).Nodup :=
  (List.nodup_finRange Q).filter _

private theorem sum_selected {R : Type*} [AddCommMonoid R]
    (s : Finset (Fin Q)) (f : Fin Q → R) : ((selected s).map f).sum = ∑ i ∈ s, f i := by
  rw [← List.sum_toFinset f (selected_nodup s), selected_toFinset]

private theorem prod_selected {R : Type*} [CommMonoid R]
    (s : Finset (Fin Q)) (f : Fin Q → R) : ((selected s).map f).prod = ∏ i ∈ s, f i := by
  rw [← List.prod_toFinset f (selected_nodup s), selected_toFinset]

def factorData (ops : RingProgram C) (cache : NodeCache C Q) (i j : Fin Q) : Factor C :=
  ⟨cache.difference i j, (ops.negRun (cache.node j)).1⟩

def termData (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q) : Term C :=
  ⟨d i, cache.inverse i, (selected (s.erase i)).map (factorData ops cache i)⟩

def rowData {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (ops : RingProgram C) (cache : NodeCache C Q)
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) : Row C :=
  ⟨if v = y then ops.oneRun.1 else ops.zeroRun.1,
    if y ∈ correctionColumns head σ R then
      (selected (mismatchPositions head σ y)).map
        (termData ops cache (mismatchPositions head σ y) (d y))
    else []⟩

def mapFactor {A : Type*} (f : C → A) (x : Factor C) : Factor A :=
  ⟨f x.inverseDifference, f x.negativeNode⟩

def mapTerm {A : Type*} (f : C → A) (x : Term C) : Term A :=
  ⟨f x.value, f x.inverseNode, x.factors.map (mapFactor f)⟩

def mapRow {A : Type*} (f : C → A) (x : Row C) : Row A :=
  ⟨f x.delta, x.terms.map (mapTerm f)⟩

section Correctness

variable [CommRing E] (ops : RepresentedRing C E) (cache : NodeCache C Q)
variable {node : Fin Q → E} (units : NodeUnits node)
variable (hnode : ∀ i, ops.decode (cache.node i) = node i)
variable (hinv : ∀ i, ops.decode (cache.inverse i) = units.nodeInverse i)
variable (hdiff : ∀ i j, ops.decode (cache.difference i j) = units.differenceInverse i j)

private theorem rowExpression_eval (r : Row (Polynomial E)) :
    (rowExpression Polynomial.X r).eval = r.delta +
      (r.terms.map (fun t => (termExpression Polynomial.X t).eval)).sum := by
  change r.delta + (Algorithm.Expr.sum (r.terms.map (termExpression Polynomial.X))).eval = _
  simp only [Algorithm.Expr.eval_sum, List.map_map, Function.comp_def]

include hnode hdiff in
private theorem factorData_eval (i j : Fin Q) :
    (factorExpression Polynomial.X
      (mapFactor (fun x => Polynomial.C (ops.decode x)) (factorData ops.program cache i j))).eval =
      basisDivisor units i j := by
  simp [factorExpression, mapFactor, factorData, Algorithm.Expr.eval, ops.neg_correct, hnode, hdiff, basisDivisor, sub_eq_add_neg]

include hnode hinv hdiff in
private theorem termData_eval (s : Finset (Fin Q)) (d : Fin Q → C) (i : Fin Q) :
    (termExpression Polynomial.X
      (mapTerm (fun x => Polynomial.C (ops.decode x)) (termData ops.program cache s d i))).eval =
      Polynomial.C (ops.decode (d i)) * SubexpRowInterpolation.basis units s i := by
  simp only [termExpression, mapTerm, termData, Algorithm.Expr.eval, Algorithm.Expr.eval_product,
    List.map_map, Function.comp_def, hinv]
  simp_rw [factorData_eval ops cache units hnode hdiff]
  rw [prod_selected]
  rfl

include hnode hinv hdiff in
theorem rowData_eval {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) :
    (rowExpression Polynomial.X
      (mapRow (fun x => Polynomial.C (ops.decode x))
        (rowData ops.program cache v head σ R d y))).eval =
      (SubexpTaylorExecution.mapCode ops.decode
        (SubexpRepresentedRows.row ops.program cache v head σ R d y)).denote := by
  rw [SubexpRepresentedRows.map_row ops cache units hnode hinv hdiff,
    mismatchRowCode_denote]
  have hdelta : ops.decode (if v = y then ops.oneRun.1 else ops.zeroRun.1) =
      (Pi.single v (1 : E) : V → E) y := by
    by_cases h : v = y
    · subst y; simp [ops.one_correct]
    · simp [h, ops.zero_correct]
  have hdelta_program : ops.decode
      (if v = y then ops.program.oneRun.1 else ops.program.zeroRun.1) =
      (Pi.single v (1 : E) : V → E) y := hdelta
  rw [rowExpression_eval]
  by_cases hy : y ∈ correctionColumns head σ R
  · simp only [mapRow, rowData, ite_eq_left hy,
      List.map_map, Function.comp_def, hdelta_program]
    simp_rw [termData_eval ops cache units hnode hinv hdiff]
    rw [sum_selected]
    simp only [mismatchRowPath, rowPath, mismatchCorrection, columnCorrection,
      ite_eq_left hy, correctionPolynomial]
  · simp [ mapRow, rowData, hy, hdelta, mismatchRowPath, rowPath, mismatchCorrection,
      columnCorrection ]

end Correctness

end SubexponentialSAT.Subexp.UniversalRowSource

end OAI.Algorithms
