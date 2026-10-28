import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRowSelection
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank

namespace OAI.Algorithms

/-! Runtime signatures may retain every raw integer row.  A row basis is
used only in this cardinality proof, never computed by the bucket program. -/
namespace SubexponentialSAT.SqrtLog.LayoutSignatureBound

open scoped BigOperators
open LayoutExactBuckets LayoutRowSelection

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] in
theorem signature_eq_of_rationalRowSpan (C : J → V → ℤ) (A : K → V → ℤ)
    (hspan : RationalRowSpan C A) (x y : V → ℤ)
    (hxy : signature A x = signature A y) : signature C x = signature C y := by
  have hz : ∀ k, signature A (x-y) k = 0 := by
    intro k
    rw [signature_sub, congrFun hxy k, sub_self]
  have hc := integer_kernel_of_rational_span C A hspan (x-y) hz
  funext j
  exact sub_eq_zero.mp (by simpa only [signature_sub] using hc j)

omit [Fintype J] in
theorem card_range_boolSignature_le_selected (C : J → V → ℤ) (select : K → J)
    (hspan : RationalRowSpan C (fun k => C (select k))) :
    Nat.card (Set.range (boolSignature C)) ≤
      Nat.card (Set.range (boolSignature (fun k => C (select k)))) := by
  classical
  let project : Set.range (boolSignature C) →
      Set.range (boolSignature (fun k => C (select k))) := fun y =>
    ⟨fun k => y.val (select k), by
      obtain ⟨x,hx⟩ := y.property
      refine ⟨x, ?_⟩
      funext k
      exact congrFun hx (select k)⟩
  apply Nat.card_le_card_of_injective project
  intro y z h
  apply Subtype.ext
  obtain ⟨x,hx⟩ := y.property
  obtain ⟨w,hw⟩ := z.property
  rw [← hx, ← hw]
  apply signature_eq_of_rationalRowSpan C (fun k => C (select k)) hspan
  funext k
  have hk := congrFun (congrArg Subtype.val h) k
  change y.val (select k) = z.val (select k) at hk
  rw [← hx, ← hw] at hk
  change signature C (fun v => if x v then 1 else 0) (select k) =
    signature C (fun v => if w v then 1 else 0) (select k)
  unfold boolSignature at hk
  exact hk

/-- Rank-sensitive bound for the FULL attained raw-signature set.  The
existential basis contributes no runtime selection or minor enumeration. -/
theorem card_range_boolSignature_le_rank (C : J → V → ℤ) (W : ℕ)
    (hC : ∀ j v, |C j v| ≤ (W : ℤ)) :
    Nat.card (Set.range (boolSignature C)) ≤
      (2 * Fintype.card V * W + 1) ^ LayoutRank.rowRank C := by
  obtain ⟨K, hK, select, hinj, hspan, hcard⟩ := exists_actual_row_basis C
  let _ : Fintype K := hK
  have h1 := card_range_boolSignature_le_selected C select hspan
  have h2 := card_range_boolSignature_le (fun k => C (select k)) W
    (fun k v => hC (select k) v)
  apply h1.trans
  rw [hcard] at h2
  exact h2

end SubexponentialSAT.SqrtLog.LayoutSignatureBound

end OAI.Algorithms
