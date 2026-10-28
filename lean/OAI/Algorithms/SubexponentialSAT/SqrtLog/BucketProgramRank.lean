import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramAttained
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRankSignature

namespace OAI.Algorithms

/-! Rank bounds the number of actual stored buckets. The primitive machine
still processes all rows and its serialization costs use their full count. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

theorem attainedKeys_signed_length_le_rank {h d : ℕ}
    (W : List Bool) (pairs : Fin d → Fin h → SignedWord) (A : Fin d → Fin h → ℤ)
    {ys : List (List (List Bool))} (js : List ℕ) (n H : ℕ)
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys)
    (hN : ∀ j i,SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W)
    (hA : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).1 : ℤ)-
      (SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 : ℤ)=A j i)
    (hbound : ∀ j i,|A j i| ≤ (H:ℤ)) :
    (attainedKeys (Label.labelled W ys js n (assignments h))).length ≤
      (2*h*H+1)^LayoutRank.rowRank A := by
  have hc := attainedKeys_signed_length_le_signature_range W pairs A js n hy hN hA
  have hr := LayoutSignatureBound.card_range_boolSignature_le_rank A H hbound
  exact hc.trans (by simpa using hr)

/-- This is the exact list passed to the stored bucket encoder by Controller:
all labelled assignments in forward order, with deduplicated keys obtained
from reverse record order. Its length obeys the rational rank bound. -/
theorem storedTable_length_le_rank {h d : ℕ}
    (W : List Bool) (pairs : Fin d → Fin h → SignedWord) (A : Fin d → Fin h → ℤ)
    {ys : List (List (List Bool))} (js : List ℕ) (n H : ℕ)
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys)
    (hN : ∀ j i,SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W)
    (hA : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).1 : ℤ)-
      (SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 : ℤ)=A j i)
    (hbound : ∀ j i,|A j i| ≤ (H:ℤ)) :
    (SubexponentialSAT.Subexp.PackingBucketTable.table
      (Label.labelled W ys js n (assignments h))
      (attainedKeys (Label.labelled W ys js n (assignments h)).reverse)).length ≤
      (2*h*H+1)^LayoutRank.rowRank A := by
  simp only [SubexponentialSAT.Subexp.PackingBucketTable.table,List.length_map,attainedKeys_reverse_length]
  exact attainedKeys_signed_length_le_rank W pairs A js n H hy hN hA hbound

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
