import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramABI
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSparse

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def weightedValue (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache
    (Squarefree.ScaleProgram.scaled p t M cache table weight jet) seed

structure AssignmentContext where
  support : List Bool
  headMask : List Bool
  head : List Bool
  bucket : List Bool

def AssignmentContext.Matches (c : AssignmentContext) (high : Fin 768 → List Bool) : Prop :=
  high 168 = c.support ∧ high 178 = c.headMask ∧
    high 175 = c.head ∧ high 177 = c.bucket

abbrev Contribution (n B d : ℕ) :=
  RingProgram.Code (Word B) d × List (Product.Entry n B d)

def headRun (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (c : AssignmentContext) : List (List Bool) → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d)
  | [], seed => seed
  | x::xs, seed => headRun p t M cache table meaning c xs
      (weightedValue p t M cache table (meaning c x).1 (meaning c x).2 seed)

def headContext (high : Fin 768 → List Bool) (h : HeadInput) : AssignmentContext :=
  ⟨high 168,h.mask,h.context,high 177⟩

def headStepValue (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (h : HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) :=
  Product.run p t M cache table u J left
    (headRun p t M cache table meaning (headContext high h) h.assignments []) []

def headsRun (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (base : Fin 768 → List Bool) : List HeadInput → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d)
  | [], left => left
  | h::hs, left => headsRun p t M cache table u J meaning base hs
      (headStepValue p t M cache table u J meaning base h left)

def supportValue (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d)) :=
  Normalize.run p t M cache (Moments.rawProject s product) seed

def supportProduct (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n)) :=
  headsRun p t M cache table u J meaning (Function.update high 168 (Squarefree.encodeMask s)) hs one

def supportsRun (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) :
    List (Finset (Fin n)) → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d)
  | [], seed => seed
  | s::ss, seed => supportsRun p t M cache table u J meaning high hs one ss
      (supportValue p t M cache s (supportProduct p t M cache table u J meaning high hs one s) seed)

def bucketsRun (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (high : Fin 768 → List Bool) (supports : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) :
    List BucketInput → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d)
  | [], seed => seed
  | b::bs, seed => bucketsRun p t M cache table u J meaning high supports one bs
      (supportsRun p t M cache table u J meaning (Function.update high 177 b.context)
        b.heads one supports seed)

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
