import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyInventory

namespace OAI.Algorithms

/-! Rank-sensitive cardinality of the actual attained Cartesian inventory.
The hypotheses constrain entry values, not the cardinalities of head tables. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open LeafHeadSetupProgram
open scoped BigOperators

def headRank (C : ℕ → ℕ → ℤ) (D n : ℕ)
    (rows : List (List Bool)) (low : List Bool) (z : ℕ) : ℕ :=
  LayoutRank.rowRank (selectedMatrix C D (selectedHeads n rows low z))

def commonBase (n H : ℕ) : ℕ := 2*n*H+1

theorem commonBase_pos (n H : ℕ) : 1 ≤ commonBase n H := by unfold commonBase; omega

theorem producedHead_length_le_rank {base : Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {table : BucketTupleProgram.HeadTable}
    (hp : ProducedHead base n N D rows low Rel B z table)
    (C : ℕ → ℕ → ℤ) (H : ℕ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v)
    (hbound : ∀ j v p,j < D→v < n→Rel j v p→|C j v| ≤ (H:ℤ)) :
    table.buckets.length ≤ (commonBase n H)^headRank C D n rows low z := by
  obtain ⟨mr,ys,hr,hy,rfl⟩ := hp
  have hj := HeadIdentifierProgram.chosenIds_bound (HeadIdentifierProgram.predicate rows low z) n
  have ht := actualBuckets_length_le_rank (base.stacks 141) n H C hr hy
    (fun j v p hj' hv hp=>hrel j v p hj' (hj v hv) hp)
    (fun j v p hj' hv hp=>hbound j v p hj' (hj v hv) hp)
  apply ht.trans
  apply Nat.pow_le_pow_left
  have hc := HeadIdentifierProgram.count_le (HeadIdentifierProgram.predicate rows low z) n
  change 2*(selectedHeads n rows low z).length*H+1 ≤ 2*n*H+1
  have hc' : (selectedHeads n rows low z).length ≤ n := hc
  gcongr

private theorem sum_succ (f : ℕ → ℕ) (z k : ℕ) :
    (∑ i : Fin (k+1),f (z+i.val))=f z+∑ i : Fin k,f ((z+1)+i.val) := by
  rw [Fin.sum_univ_succ]
  simp [Nat.add_left_comm,Nat.add_comm]

/-- The product in `enumerate_length` is bounded using the rank of every
literal selected matrix, in the producer's consecutive head order. -/
theorem producedHeads_product_le_rankSum {base : Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {tables : List BucketTupleProgram.HeadTable}
    (hp : ProducedHeads base n N D rows low Rel B z tables)
    (C : ℕ → ℕ → ℤ) (H : ℕ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v)
    (hbound : ∀ j v p,j < D→v < n→Rel j v p→|C j v| ≤ (H:ℤ)) :
    (tables.map fun table=>table.buckets.length).prod ≤
      (commonBase n H)^(∑ i : Fin tables.length,headRank C D n rows low (z+i.val)) := by
  induction hp with
  | nil => simp
  | @cons z table tables hh ht ih =>
    have hh' := producedHead_length_le_rank hh C H hrel hbound
    simp only [List.map_cons,List.prod_cons,List.length_cons,sum_succ,pow_add]
    exact Nat.mul_le_mul hh' ih

theorem producedHeads_enumerate_le_rankSum {base : Data} {n N D : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {tables : List BucketTupleProgram.HeadTable}
    (hp : ProducedHeads base n N D rows low Rel B z tables)
    (C : ℕ → ℕ → ℤ) (H : ℕ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v)
    (hbound : ∀ j v p,j < D→v < n→Rel j v p→|C j v| ≤ (H:ℤ)) :
    (BucketTupleProgram.enumerate tables).length ≤
      (commonBase n H)^(∑ i : Fin tables.length,headRank C D n rows low (z+i.val)) := by
  rw [BucketTupleProgram.enumerate_length]
  exact producedHeads_product_le_rankSum hp C H hrel hbound

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
