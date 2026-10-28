import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankFiber
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankTables
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrixNatural

namespace OAI.Algorithms

/-! The native fiber relation realizes the literal owner-sum matrix. Signed
component mass bounds imply both safe shifting and a signature-height bound. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q D n : ℕ}

def entryNat (P : PackingData (Fin D) (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (j i : ℕ) : ℤ :=
  if hj : j < D then if hi : i < D then
    LayoutProgram.localEntry P A R t ⟨j,hj⟩ ⟨i,hi⟩ else 0 else 0

def FiberRel (ps : List (ℕ × ℕ)) (value : ℕ → ℕ → ℤ) (H : ℕ)
    (j v : ℕ) (p : LayoutMatrixProgram.Pair) : Prop :=
  RowSelectionProgram.pairValue p=
    ((LayoutOwnerFiberProgram.fiberIndices v 0 ps).map (value j)).sum ∧
  RowSelectionProgram.pairTotal p.1 p.2 ≤ H

theorem fiber_value_literal (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val)
    (j : Fin D) (v : Fin n) :
    ((LayoutOwnerFiberProgram.fiberIndices v.val 0 (List.ofFn ps)).map
      (entryNat P A R t j.val)).sum=LayoutProducedMatrix.literalNat P owner A R t j.val v.val := by
  rw [LayoutProducedMatrix.literalNat_fin]
  exact fiber_sum_eq_matrix owner ps hp (LayoutProgram.localEntry P A R t)
    (entryNat P A R t) (by intro j i; simp [entryNat]) j v

theorem pair_abs_le_mass (p : LayoutMatrixProgram.Pair) (H : ℕ)
    (hp : RowSelectionProgram.pairTotal p.1 p.2 ≤ H) :
    |RowSelectionProgram.pairValue p| ≤ (H:ℤ) := by
  unfold RowSelectionProgram.pairTotal at hp
  unfold RowSelectionProgram.pairValue RowSelectionProgram.signedValue
  have hp' : (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)+
      (SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ) ≤ (H:ℤ) := by exact_mod_cast hp
  have h1 := Int.natCast_nonneg (SubexponentialSAT.BinaryArithmetic.toNat p.1)
  have h2 := Int.natCast_nonneg (SubexponentialSAT.BinaryArithmetic.toNat p.2)
  rw [abs_le]
  omega

theorem fiberRel_realizes (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val)
    (H : ℕ) (j v : ℕ) (p : LayoutMatrixProgram.Pair) (hj : j < D) (hv : v < n)
    (hr : FiberRel (List.ofFn ps) (entryNat P A R t) H j v p) :
    RowSelectionProgram.pairValue p=LayoutProducedMatrix.literalNat P owner A R t j v ∧
    |LayoutProducedMatrix.literalNat P owner A R t j v| ≤ (H:ℤ) := by
  have he := hr.1.trans (fiber_value_literal P owner A R t ps hp ⟨j,hj⟩ ⟨v,hv⟩)
  exact ⟨he,he ▸ pair_abs_le_mass p H hr.2⟩

/-- A single physical head table is bounded by the rank of its literal
selected integer matrix, in exactly the emitted column order. -/
theorem producedHead_fiber_length {base : LeafHeadSetupProgram.Data} {N B z : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val) (H : ℕ)
    {table : BucketTupleProgram.HeadTable}
    (ht : LeafHeadSetupProgram.ProducedHead base n N D rows low
      (FiberRel (List.ofFn ps) (entryNat P A R t) H) B z table)
    (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    table.buckets.length ≤ (commonBase n H)^
      headRank (LayoutProducedMatrix.literalNat P owner A R t) D n rows low z := by
  apply producedHead_length_le_rank ht (LayoutProducedMatrix.literalNat P owner A R t) H
  · intro j v p hj hv hr
    have he := fiberRel_realizes P owner A R t ps hp H j v p hj hv hr
    refine ⟨?_,he.1⟩
    have hm := hr.2
    unfold RowSelectionProgram.pairTotal at hm
    omega
  · intro j v p hj hv hr
    exact (fiberRel_realizes P owner A R t ps hp H j v p hj hv hr).2

/-- The actual r-table product, obtained from an original-address fiber
entry relation. No head-cardinality bounds are hypotheses. -/
theorem producedHeads_fiber_product {base : LeafHeadSetupProgram.Data} {N B : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hp : ∀ i,(ps i).1=(owner i).val) (H : ℕ)
    {tables : List BucketTupleProgram.HeadTable}
    (ht : LeafHeadSetupProgram.ProducedHeads base n N D rows low
      (FiberRel (List.ofFn ps) (entryNat P A R t) H) B (t.val*r) tables)
    (hlen : tables.length=r) (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    (tables.map fun table=>table.buckets.length).prod ≤ (commonBase n H)^
      (∑ g : Fin r,headRank (LayoutProducedMatrix.literalNat P owner A R t)
        D n rows low (t.val*r+g.val)) := by
  subst r
  have hh := producedHeads_product_le_rankSum ht
    (LayoutProducedMatrix.literalNat P owner A R t) H
    (fun j v p hj hv hr=>by
      have he := fiberRel_realizes P owner A R t ps hp H j v p hj hv hr
      refine ⟨?_,he.1⟩
      have hm := hr.2
      unfold RowSelectionProgram.pairTotal at hm
      omega)
    (fun j v p hj hv hr=>(fiberRel_realizes P owner A R t ps hp H j v p hj hv hr).2)
  exact hh

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
