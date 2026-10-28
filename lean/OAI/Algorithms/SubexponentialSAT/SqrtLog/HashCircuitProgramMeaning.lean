import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramArithmeticNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramDynamicFold

namespace OAI.Algorithms

/-! Exact pure result functions of the fixed native hash interpreter. The
execution proofs live in HashCircuitProgramInterpreter; no alternate evaluator
or operation oracle is introduced here. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one payload left : List (Product.Entry n (baseWidth p t) d))

def negative : List (Product.Entry n (baseWidth p t) d) :=
  Normalize.run p t M cache
    (Squarefree.ScaleProgram.scaled p t M cache table minusOne payload) one

def value (positive : Bool) : List (Product.Entry n (baseWidth p t) d) :=
  if positive then negative p t M cache table minusOne one payload else payload

def result (u J : ℕ) (positive : Bool) : List (Product.Entry n (baseWidth p t) d) :=
  Product.run p t M cache table u J left (value p t M cache table minusOne one payload positive) []

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (u J : ℕ)

def step (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  LiteralCallback.result p t M cache table minusOne one (incidence l.variable) acc u J l.positive

def literalBits {n : ℕ} (l : SAT.Literal (Fin n)) := Encoding.encodeNat (Encoding.literalCode l)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
structure WeightedClause (n B d : ℕ) where
  scalar : RingProgram.Code (Word B) d
  literals : List (SAT.Literal (Fin n))

def literalList {n B d : ℕ} (w : WeightedClause n B d) : List Bool :=
  Encoding.encodeList id (w.literals.map Clause.literalBits)
def payload {n B d : ℕ} (w : WeightedClause n B d) : List Bool :=
  Encoding.frame (RingProgram.flat w.scalar) ++ literalList w

/-- The supplied clause bytes are the original canonical literal list. -/
theorem literalList_eq {n B d : ℕ} (w : WeightedClause n B d) :
    literalList w = Encoding.encodeList Encoding.encodeNat (w.literals.map Encoding.literalCode) := by
  cases w with
  | mk scalar ls =>
    dsimp [literalList]
    induction ls with
    | nil => rfl
    | cons l ls ih =>
      simpa [Encoding.encodeList,Clause.literalBits] using
        (congrArg (fun xs => true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++ xs)) ih)

/-- This is exactly the byte schema emitted by the upstream row materializer. -/
theorem payload_eq_weightedPayload {n B d : ℕ} (w : WeightedClause n B d) :
    payload w = Rows.weightedPayload (RingProgram.flat w.scalar) (w.literals.map Encoding.literalCode) := by
  rw [payload,literalList_eq]
  rfl

variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (u J : ℕ)

def clauseValue (w : WeightedClause n (baseWidth p t) d) :=
  DynamicFold.value (Clause.step p t M cache table minusOne one incidence u J) w.literals one

def value (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache (Squarefree.ScaleProgram.scaled p t M cache table w.scalar
    (clauseValue p t M cache table minusOne one incidence u J w)) acc

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
