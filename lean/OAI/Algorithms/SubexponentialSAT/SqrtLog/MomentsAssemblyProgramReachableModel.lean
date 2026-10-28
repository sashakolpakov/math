import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRelReadout

namespace OAI.Algorithms

/-! Bounded frame requirements for states reached by the existing native
loops. These definitions do not quantify unrestricted parser payloads. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable
open MomentsProgram

def AssignmentFrames (valid : (Fin 768 → List Bool) → Prop)
    (base : Fin 768 → List Bool) (xs : List (List Bool)) : Prop :=
  ∀ source : List Bool, source.length ≤ (rawFrames xs).length →
    ∀ x ∈ xs, valid (Function.update (Function.update base 160 source) 174 x)

def HeadFrames (valid : (Fin 768 → List Bool) → Prop)
    (base : Fin 768 → List Bool) (hs : List HeadInput) : Prop :=
  ∀ h ∈ hs, ∀ tail : List Bool,
    tail.length ≤ (rawFrames (hs.map HeadInput.bits)).length →
    AssignmentFrames valid (headHigh base h tail) h.assignments

def SupportFrames {n : ℕ} (B d : ℕ) (vars : Finset (Fin n)) (u J : ℕ)
    (valid : (Fin 768 → List Bool) → Prop) (base : Fin 768 → List Bool)
    (ss : List (Finset (Fin n))) (hs : List HeadInput) : Prop :=
  ∀ seed : List (Product.Entry n B d), EntryInvariant vars u J seed →
    ∀ source : List Bool, source.length ≤ (rawFrames (ss.map Squarefree.encodeMask)).length →
    ∀ s ∈ ss, ∀ tail : List Bool,
      tail.length ≤ (rawFrames (ss.map Squarefree.encodeMask)).length →
      HeadFrames valid
        (supportHigh (supportStream base (Product.bytes seed) source) (Squarefree.encodeMask s) tail) hs

def BucketFrames {n : ℕ} (B d : ℕ) (vars : Finset (Fin n)) (u J : ℕ)
    (valid : (Fin 768 → List Bool) → Prop) (base : Fin 768 → List Bool)
    (ss : List (Finset (Fin n))) (bs : List BucketInput) : Prop :=
  ∀ seed : List (Product.Entry n B d), EntryInvariant vars u J seed →
    ∀ source : List Bool, source.length ≤ (bucketsInput bs).length →
    ∀ b ∈ bs, ∀ tail : List Bool, tail.length ≤ (bucketsInput bs).length →
      SupportFrames B d vars u J valid (bucketHigh (bucketStream base (Product.bytes seed) source) b tail) ss b.heads

end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational.Reachable

end OAI.Algorithms
