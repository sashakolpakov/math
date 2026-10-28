import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramCostModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramInterpreter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramWorkBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLookupBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics

namespace OAI.Algorithms

/-! Explicit polynomial envelopes for the concrete native raw-hash interpreter.
S bounds the number of retained keys; B and d are actual encoded coefficient
width and extension dimension. No arithmetic or parser callback is free. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Native
open LeafProgram.NativeSemantics

variable {n B d u J S : ℕ} {vars : Finset (Fin n)}

theorem good_length {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S) : a.length ≤ S :=
  h.length_le.trans hS

theorem good_keyBound {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) a := by
  intro x hx
  have hh := Squarefree.encodeIndex_length_le x.1 (h.valid x hx).1
  omega

theorem good_bytes {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S) :
    (Product.bytes a).length ≤ bytesBound B d n u J S := by
  exact (Product.bytes_length_le a (n+u+J) (good_keyBound h)).trans
    (Nat.mul_le_mul_right _ (good_length h hS))

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S)

include hS in
omit [Fact (Nat.Prime p)] in
theorem scale_le (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex a ≤ scaleBound (baseWidth p t) d n u J S := by
  have h := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex a (n+u+J) (good_keyBound ha)
  have hmul := Nat.mul_le_mul_right
    (40000*(d+1)^3*(baseWidth p t+1)^2+35*(d*baseWidth p t)+7*d+22*(n+u+J)+57)
    (good_length ha hS)
  unfold scaleBound
  omega

include hS in
theorem normalize_le (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good vars u J source) (hi : Good vars u J seed) :
    Normalize.work p t M cache Squarefree.encodeIndex source seed ≤ normalizeBound (baseWidth p t) d n u J S := by
  have hsl := good_length hs hS
  have hil := good_length hi hS
  have h := Normalize.work_le p t M cache Squarefree.encodeIndex (n+u+J) (2*S) source seed
    (good_keyBound hs) (good_keyBound hi) (by omega)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hsl) 1)

include hS in
theorem product_le (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Product.work p t M cache table u J left right [] ≤ productBound (baseWidth p t) d n u J S := by
  have hll := good_length hl hS
  have hrl := good_length hr hS
  have h := Product.work_le p t M cache table u J (S*S) left right []
    (fun a ha => (hl.valid a ha).1) (fun a ha => (hr.valid a ha).1)
    (by intro a ha; simp at ha) (by simpa using Nat.mul_le_mul hll hrl)
  have hm : Product.stepEnvelope (baseWidth p t) d n u J (S*S) right.length ≤
      Product.stepEnvelope (baseWidth p t) d n u J (S*S) S := by
    unfold Product.stepEnvelope
    dsimp only
    gcongr
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul hll (Nat.add_le_add_right hm 2)) 1)

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (degree : List Bool) (hd : degree.length = d)

include hS hone hd in
theorem negative_le (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
    LiteralCallback.negateBudget p t M cache table minusOne one a degree ≤
      negativeBound (baseWidth p t) d n u J S := by
  have hba := good_bytes ha hS
  have hbo := good_bytes hone hS
  have hneg := literal_good p t M cache table vars u J minusOne one hone a ha true
  have hbn := good_bytes hneg hS
  have hsc := scale_le p t hS a ha
  have hno := normalize_le p t M cache hS
    (Squarefree.ScaleProgram.scaled p t M cache table minusOne a) one
    (scaled_good p t M cache table vars u J minusOne a ha) hone
  simp only [LiteralCallback.value,ite_true] at hbn
  unfold LiteralCallback.negateBudget negativeBound
  simp only [RingProgram.flat_length,hd]
  omega

/-- The table consists of one actual serialized incidence dictionary for each
original variable. It is the same table for every literal occurrence. -/
def entries (incidence : Fin n → List (Product.Entry n B d)) : List (List Bool × List Bool) :=
  incidenceEntries (fun (_ : Unit) v => Product.bytes (incidence v)) ()

include hS hone hi hd in
theorem literal_le (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d))
    (ha : Good vars u J acc) :
    Clause.cost p t M cache table minusOne one incidence degree u J (entries incidence) l acc ≤
      literalBound (baseWidth p t) d n u J S := by
  have hba := good_bytes ha hS
  have hbp := good_bytes (hi l.variable) hS
  have hc := literal_good p t M cache table vars u J minusOne one hone
    (incidence l.variable) (hi l.variable) l.positive
  have hbc := good_bytes hc hS
  have hres := product_good p t M cache table vars u J acc _ ha hc
  have hbr := good_bytes hres hS
  have hn := negative_le p t M cache table hS minusOne one hone degree hd
    (incidence l.variable) (hi l.variable)
  have hp := product_le p t M cache table hS acc _ ha hc
  have hf := LookupBounds.incidence_fetch_budget
    (fun (_ : Unit) v => Product.bytes (incidence v)) () (bytesBound (baseWidth p t) d n u J S)
    (fun v => good_bytes (hi v) hS) l.variable
  have hv := l.variable.isLt
  unfold Clause.cost LiteralCallback.budget literalBound fetchBound
  dsimp only [entries] at *
  simp only [LiteralCallback.result] at hbr ⊢
  split_ifs <;> omega

include hS hone hi hd in
/-- Fixed-width clause traversal with the actual lookup and arithmetic costs. -/
theorem clause_le (ls : List (SAT.Literal (Fin n))) (acc : List (Product.Entry n (baseWidth p t) d))
    (ha : Good vars u J acc) :
    DynamicFold.work Clause.literalBits (Clause.step p t M cache table minusOne one incidence u J)
      (Clause.cost p t M cache table minusOne one incidence degree u J (entries incidence)) ls acc ≤
      ls.length*(6*(2*n+1)+literalBound (baseWidth p t) d n u J S+7) := by
  apply DynamicFold.work_le_invariant _ _ _ (Good vars u J) _ _ _ _ ha
  · intro l hl; exact Row.literalBits_length l
  · intro l hl a h
    exact step_good p t M cache table vars u J minusOne one incidence hone hi l a h
  · intro l hl a h
    exact literal_le p t M cache table hS minusOne one incidence hone hi degree hd l a h

include hS hone hi hd in
/-- A weighted clause includes parsing, clause evaluation, scalar multiplication,
normalization into the row accumulator, and physical frame cleanup. -/
theorem row_le (w : Row.WeightedClause n (baseWidth p t) d)
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc)
    (k : ℕ) (hk : w.literals.length ≤ k) :
    Row.cost p t M cache table minusOne one incidence degree u J (entries incidence) w acc ≤
      rowBound (baseWidth p t) d n u J S k := by
  have hpay := Row.payload_length w k hk
  have hbo := good_bytes hone hS
  have hba := good_bytes ha hS
  have hc := clause_fold_good p t M cache table vars u J minusOne one incidence hone hi w.literals one hone
  have hbc := good_bytes hc hS
  have hr := row_step_good p t M cache table vars u J minusOne one incidence hone hi w acc ha
  have hbr := good_bytes hr hS
  have hclause := clause_le p t M cache table hS minusOne one incidence hone hi degree hd w.literals one hone
  have hclause' := hclause.trans (Nat.mul_le_mul_right _ hk)
  have hscale := scale_le p t hS _ hc
  have hnorm := normalize_le p t M cache hS _ acc
    (scaled_good p t M cache table vars u J w.scalar _ hc) ha
  unfold Row.cost rowBound payloadBound
  dsimp only [Row.clauseValue] at *
  simp only [RingProgram.flat_length,hd]
  omega

include hS hone hi hd in
theorem program_le (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (k : ℕ) (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    7+DynamicFold.work Row.payload (Row.value p t M cache table minusOne one incidence u J)
      (Row.cost p t M cache table minusOne one incidence degree u J (entries incidence)) ws [] ≤
      programBound (baseWidth p t) d n u J S k ws.length := by
  have h := DynamicFold.work_le_invariant Row.payload
    (Row.value p t M cache table minusOne one incidence u J)
    (Row.cost p t M cache table minusOne one incidence degree u J (entries incidence))
    (Good vars u J) ws [] (payloadBound (baseWidth p t) d n k)
    (rowBound (baseWidth p t) d n u J S k) Good.nil
    (fun w hw => Row.payload_length w k (hk w hw))
    (fun w hw a ha => row_step_good p t M cache table vars u J minusOne one incidence hone hi w a ha)
    (fun w hw a ha => row_le p t M cache table hS minusOne one incidence hone hi degree hd w a ha k (hk w hw))
  exact Nat.add_le_add_left h 7

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
