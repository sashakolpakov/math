import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Attained-signature DFS cardinalities and work

A level is indexed by its attained signatures, not its Boolean assignments or
an ambient rectangular range of raw row values. These finite types describe
visits mathematically; no family or product is materialized by these definitions.
The native encoded-frame traversal is a separate refinement obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS

open scoped BigOperators

/-- Partial tuples indexing invocations of the generator at the next level. -/
abbrev Prefix (A : ℕ → Type*) (depth : ℕ) := (i : Fin depth) → A i.val

/-- A complete tuple of emitted representatives is in bijection with the
product of the actual attained full signatures. This records visit-once
semantics without choosing or enumerating independent matrix rows. -/
noncomputable def attainedTupleEquiv {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (N i) → κ i) (depth : ℕ) :
    Prefix (fun i => AttainedSignatures.Representative (key i)) depth ≃
      Prefix (fun i => Set.range (key i)) depth :=
  Equiv.piCongrRight fun i => AttainedSignatures.representativeEquiv (key i.val)

theorem card_attainedTuple {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (N i) → κ i) (depth : ℕ) :
    Nat.card (Prefix (fun i => AttainedSignatures.Representative (key i)) depth) =
      Nat.card (Prefix (fun i => Set.range (key i)) depth) :=
  Nat.card_congr (attainedTupleEquiv key depth)

/-- Number of partial tuples at a specified depth. -/
def prefixCount (K : ℕ → ℕ) (depth : ℕ) : ℕ :=
  ∏ i ∈ Finset.range depth, K i

/-- Exact cardinality of the partial-tuple domain. -/
theorem card_prefix (A : ℕ → Type*) [∀ i, Fintype (A i)] (depth : ℕ) :
    Fintype.card (Prefix A depth) = prefixCount (fun i => Fintype.card (A i)) depth := by
  rw [Fintype.card_pi]
  exact Fin.prod_univ_eq_prod_range (fun i => Fintype.card (A i)) depth

@[simp] theorem prefixCount_zero (K : ℕ → ℕ) : prefixCount K 0 = 1 := by
  simp [prefixCount]

@[simp] theorem prefixCount_succ (K : ℕ → ℕ) (depth : ℕ) :
    prefixCount K (depth + 1) = prefixCount K depth * K depth := by
  exact Finset.prod_range_succ K depth

/-- Empty heads contribute one key, so every factor is at least one. -/
theorem prefixCount_le (K : ℕ → ℕ) {depth levels : ℕ} (hd : depth ≤ levels)
    (hK : ∀ i < levels, 1 ≤ K i) : prefixCount K depth ≤ prefixCount K levels := by
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hd)
  intro i hi _
  exact hK i (Finset.mem_range.mp hi)

/-- One full invocation cost for each earlier emitted partial tuple. The
cost includes reset, unsuccessful predecessor scans, and generator cleanup. -/
def generatorWork (K cost : ℕ → ℕ) (levels : ℕ) : ℕ :=
  ∑ i ∈ Finset.range levels, prefixCount K i * cost i

/-- The weighted number of generator invocations is precisely the sum over
all attained-key prefixes, with one invocation at each internal tree node. -/
theorem generatorWork_eq_sum_invocations (A : ℕ → Type*) [∀ i, Fintype (A i)]
    (cost : ℕ → ℕ) (levels : ℕ) :
    (∑ invocation : (Σ i : Fin levels, Prefix A i.val), cost invocation.1.val) =
      generatorWork (fun i => Fintype.card (A i)) cost levels := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_prefix]
  exact Fin.sum_univ_eq_sum_range
    (fun i => prefixCount (fun j => Fintype.card (A j)) i * cost i) levels

/-- Uniform cost bound for all generator invocations in a DFS. -/
theorem generatorWork_le (K cost : ℕ → ℕ) (levels bound : ℕ)
    (hK : ∀ i < levels, 1 ≤ K i) (hc : ∀ i < levels, cost i ≤ bound) :
    generatorWork K cost levels ≤ levels * prefixCount K levels * bound := by
  calc
    generatorWork K cost levels ≤
        ∑ _i ∈ Finset.range levels, prefixCount K levels * bound := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul
        (prefixCount_le K (Nat.le_of_lt (Finset.mem_range.mp hi)) hK)
        (hc i (Finset.mem_range.mp hi))
    _ = levels * prefixCount K levels * bound := by
      simp [Nat.mul_assoc]

/-- The extra predecessor rescans square each head's assignment count, but
never take the product of the assignment counts across different heads. -/
theorem generatorWork_le_four_pow (K cost h : ℕ → ℕ) (levels poly hmax : ℕ)
    (hK : ∀ i < levels, 1 ≤ K i)
    (hc : ∀ i < levels, cost i ≤ poly * 4 ^ h i)
    (hh : ∀ i < levels, h i ≤ hmax) :
    generatorWork K cost levels ≤ poly * levels * prefixCount K levels * 4 ^ hmax := by
  have hb := generatorWork_le K cost levels (poly * 4 ^ hmax) hK
    (fun i hi => (hc i hi).trans
      (Nat.mul_le_mul_left poly (Nat.pow_le_pow_right (by decide) (hh i hi))))
  calc
    generatorWork K cost levels ≤ levels * prefixCount K levels * (poly * 4 ^ hmax) := hb
    _ = poly * levels * prefixCount K levels * 4 ^ hmax := by ring

/-- The work of rescanning each group at each attained tuple. The Boolean
assignment factor is a sum over heads, never a product over heads. -/
theorem groupRescans_le (K : ℕ → ℕ) (h : ℕ → ℕ) (levels hmax : ℕ)
    (hh : ∀ i < levels, h i ≤ hmax) :
    prefixCount K levels * (∑ i ∈ Finset.range levels, 2 ^ h i) ≤
      levels * prefixCount K levels * 2 ^ hmax := by
  have hs : (∑ i ∈ Finset.range levels, 2 ^ h i) ≤ levels * 2 ^ hmax := by
    calc
      _ ≤ ∑ _i ∈ Finset.range levels, 2 ^ hmax := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right (by decide) (hh i (Finset.mem_range.mp hi))
      _ = levels * 2 ^ hmax := by simp
  calc
    _ ≤ prefixCount K levels * (levels * 2 ^ hmax) := Nat.mul_le_mul_left _ hs
    _ = levels * prefixCount K levels * 2 ^ hmax := by ring

/-- Preserve the existing rational-rank charge for the attained-key product. -/
theorem prefixCount_le_rank (K rank : ℕ → ℕ) (levels base : ℕ)
    (hK : ∀ i < levels, K i ≤ base ^ rank i) :
    prefixCount K levels ≤ base ^ (∑ i ∈ Finset.range levels, rank i) := by
  calc
    prefixCount K levels ≤ ∏ i ∈ Finset.range levels, base ^ rank i := by
      exact Finset.prod_le_prod (fun i hi => hK i (Finset.mem_range.mp hi))
    _ = base ^ (∑ i ∈ Finset.range levels, rank i) :=
      Finset.prod_pow_eq_pow_sum _ _ _

/-- Charge both the generator traversal and a full group rescan at every
complete tuple. `leafCost` includes arithmetic and accumulator updates. -/
theorem totalWork_le (K cost : ℕ → ℕ) (levels bound leafCost : ℕ)
    (hK : ∀ i < levels, 1 ≤ K i) (hc : ∀ i < levels, cost i ≤ bound) :
    generatorWork K cost levels + prefixCount K levels * leafCost ≤
      prefixCount K levels * (levels * bound + leafCost) := by
  calc
    generatorWork K cost levels + prefixCount K levels * leafCost ≤
        levels * prefixCount K levels * bound + prefixCount K levels * leafCost :=
      Nat.add_le_add_right (generatorWork_le K cost levels bound hK hc) _
    _ = prefixCount K levels * (levels * bound + leafCost) := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleDFS
