import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSquarefree

namespace OAI.Algorithms

/-! Boolean coordinate assembly and actual head weights. This avoids field
coordinates or residue representatives: head values are genuine Boolean bits. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V G R : Type*} [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G]

def Head (head : V → G) (g : G) := {v : V // head v = g}

def assemble (head : V → G) (a : ∀ g, Head head g → Bool) : V → Bool :=
  fun v => a (head v) ⟨v, rfl⟩

def split (head : V → G) (a : V → Bool) : ∀ g, Head head g → Bool :=
  fun _ v => a v.val

/-- Every Boolean assignment is exactly one tuple of independent head values. -/
def headEquiv (head : V → G) : (V → Bool) ≃ (∀ g, Head head g → Bool) where
  toFun := split head
  invFun := assemble head
  left_inv a := rfl
  right_inv a := by
    funext g v
    rcases v with ⟨v, hv⟩
    cases hv
    rfl

variable [CommSemiring R]

def localBoolWeight (head : V → G) (s : Support V) (g : G)
    (a : Head head g → Bool) : R :=
  ∏ v ∈ s.vars, if h : head v = g then (if a ⟨v, h⟩ then 1 else 0) else 1

omit [Fintype V] [DecidableEq V] in
theorem boolWeight_partition (head : V → G) (s : Support V)
    (a : ∀ g, Head head g → Bool) :
    weight (boolValue (R := R) (assemble head a)) s.vars =
      ∏ g, localBoolWeight (R := R) head s g (a g) := by
  classical
  symm
  unfold localBoolWeight
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Finset.prod_eq_single (head v)]
  · simp [ boolValue, assemble]
    rfl
  · intro g hg hne
    simp [Ne.symm hne]
  · intro hnot
    simp at hnot

omit [Fintype V] [DecidableEq V] in
/-- The same identity for actual bucket subtypes, through their Boolean values. -/
theorem boolWeight_partition_values (head : V → G)
    {X : G → Type*} (value : ∀ g, X g → Head head g → Bool)
    (s : Support V) (a : ∀ g, X g) :
    weight (boolValue (R := R) (assemble head (fun g => value g (a g)))) s.vars =
      ∏ g, localBoolWeight (R := R) head s g (value g (a g)) :=
  boolWeight_partition head s (fun g => value g (a g))

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
