import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.SAT

/-! Exact disjoint conditioning and bounded-width accumulation on original variables.
The finite sums below specify the stream; they are not materialized by its program.
The source is the sparse-query proof in counting-k-sat.tex, lines 1636–1698. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceStream

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count over the complement, including every unused declared coordinate. -/
def branchCount (H : Finset V) (P : (V → Bool) → Prop) [DecidablePred P]
    (a : H → Bool) : ℕ :=
  ∑ b : {v : V // v ∉ H} → Bool, if P (glue H a b) then 1 else 0

theorem sum_branchCount (H : Finset V) (P : (V → Bool) → Prop) [DecidablePred P] :
    ∑ a, branchCount H P a = ∑ x : V → Bool, if P x then 1 else 0 :=
  (count_predicate_split H P).symm

theorem partial_count_le (H : Finset V) (P : (V → Bool) → Prop) [DecidablePred P]
    (emitted : Finset (H → Bool)) :
    ∑ a ∈ emitted, branchCount H P a ≤ 2 ^ Fintype.card V := by
  calc
    _ ≤ ∑ a, branchCount H P a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = ∑ x : V → Bool, if P x then 1 else 0 := sum_branchCount H P
    _ ≤ ∑ _x : V → Bool, 1 := Finset.sum_le_sum (by intros; split <;> omega)
    _ = _ := by simp

theorem branchCount_true (H : Finset V) (a : H → Bool) :
    branchCount H (fun _ => True) a = 2 ^ (Fintype.card V - H.card) := by
  simp [branchCount]

theorem count_eq_sum_branches (F : SAT.CNF V) (H : Finset V) :
    SAT.count F = ∑ a, branchCount H (fun x => F.eval x = true) a := by
  rw [sum_branchCount]
  exact Finset.card_filter (fun x => F.eval x = true) Finset.univ

/-- A binary carry does not enlarge a bounded word unless the numerical result overflows.
This also permits leading zeroes, so the existing actual adder needs no normalization. -/
theorem length_carryAdd_of_lt (width : ℕ) (c : Bool) (xs : List Bool)
    (hx : xs.length ≤ width) (hv : toNat xs + bitVal c < 2 ^ width) :
    (carryAdd c xs).length ≤ width := by
  induction width generalizing c xs with
  | zero =>
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs
      cases c <;> simp_all [carryAdd, bitVal]
  | succ width ih =>
      cases xs with
      | nil => cases c <;> simp [carryAdd]
      | cons b xs =>
          have hx' : xs.length ≤ width := by simpa using hx
          have hf := fullAdder_correct false b c
          simp only [bitVal_false, zero_add] at hf
          have hv' : toNat xs + bitVal (carryBit false b c) < 2 ^ width := by
            simp only [toNat_cons, pow_succ] at hv
            omega
          simpa only [carryAdd, List.length_cons, Nat.succ_le_succ_iff] using ih
            (carryBit false b c) xs hx' hv'

theorem length_addCarry_of_lt (width : ℕ) (c : Bool) (xs ys : List Bool)
    (hx : xs.length ≤ width) (hy : ys.length ≤ width)
    (hv : toNat xs + toNat ys + bitVal c < 2 ^ width) :
    (addCarry c xs ys).length ≤ width := by
  induction width generalizing c xs ys with
  | zero =>
      have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hys : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst xs; subst ys
      cases c <;> simp_all [addCarry, carryAdd, bitVal]
  | succ width ih =>
      cases xs with
      | nil => exact length_carryAdd_of_lt (width + 1) c ys hy (by simpa using hv)
      | cons a xs =>
          have hx' : xs.length ≤ width := by simpa using hx
          cases ys with
          | nil =>
              have hf := fullAdder_correct a false c
              simp only [bitVal_false, add_zero] at hf
              have hv' : toNat xs + toNat [] + bitVal (carryBit a false c) < 2 ^ width := by
                simp only [toNat_cons, toNat_nil, add_zero, pow_succ] at hv ⊢
                omega
              simpa only [addCarry, List.length_cons, Nat.succ_le_succ_iff] using
                ih (carryBit a false c) xs [] hx' (by simp) hv'
          | cons b ys =>
              have hy' : ys.length ≤ width := by simpa using hy
              have hf := fullAdder_correct a b c
              have hv' : toNat xs + toNat ys + bitVal (carryBit a b c) < 2 ^ width := by
                simp only [toNat_cons, pow_succ] at hv
                omega
              simpa only [addCarry, List.length_cons, Nat.succ_le_succ_iff] using
                ih (carryBit a b c) xs ys hx' hy' hv'

theorem length_add_of_lt (width : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ width) (hy : ys.length ≤ width)
    (hv : toNat xs + toNat ys < 2 ^ width) :
    (add xs ys).length ≤ width :=
  length_addCarry_of_lt width false xs ys hx hy (by simpa using hv)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceStream
