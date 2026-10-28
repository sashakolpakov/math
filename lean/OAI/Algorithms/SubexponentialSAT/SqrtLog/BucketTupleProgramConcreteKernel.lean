import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignedSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankLiteral

namespace OAI.Algorithms

/-! The key used by the physical head controller has exactly the kernel of
the full emitted integer matrix, including zero rows. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

open BucketProgram
open scoped BigOperators

theorem signedKey_eq_iff {h D : ℕ} (W : List Bool)
    (pairs : Fin D → Fin h → SignedWord) (C : Fin D → Fin h → ℤ)
    {ys : List (List (List Bool))}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys)
    (hN : ∀ j i,SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W)
    (hC : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).1 : ℤ)-
      (SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 : ℤ)=C j i)
    (x y : Fin h → Bool) :
    Label.key W (List.ofFn x) ys=Label.key W (List.ofFn y) ys ↔
      ∀ j, (∑ i,C j i*(if x i then 1 else 0))=(∑ i,C j i*(if y i then 1 else 0)) := by
  obtain ⟨c,rfl,hc⟩ := shiftedMatrix_typed W pairs hy
  apply signatureValue_exact_iff W c C x y
  intro j i
  have hv := shiftedWord_integer W (pairs j i) (c j i) (hc j i) (hN j i)
  simpa only [hC j i] using hv

def KeyKernel (C : ℕ → ℕ → ℤ) (D : ℕ) (js : List ℕ) (W : List Bool)
    (ys : List (List (List Bool))) : Prop :=
  ∀ x y : Fin js.length → Bool,
    Label.key W (List.ofFn x) ys=Label.key W (List.ofFn y) ys ↔
      ∀ j : Fin D, (∑ i,C j.val (js.get i)*(if x i then 1 else 0))=
        (∑ i,C j.val (js.get i)*(if y i then 1 else 0))

theorem matrix_keyKernel {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {matrixRows : List (List LayoutMatrixProgram.Pair)}
    (W : List Bool) {ys : List (List (List Bool))} (C : ℕ → ℕ → ℤ)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js matrixRows)
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W)) matrixRows ys)
    (hrel : ∀ j v p,j < D→v∈js→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v) :
    KeyKernel C D js W ys := by
  obtain ⟨pairs,rfl,hpairs⟩ := ProducedRank.matrixRel_typed hr
  have hp (j : Fin D) (i : Fin js.length) :=
    hrel j.val (js.get i) (pairs j i) j.isLt (List.get_mem ..) (hpairs j i).1
  intro x y
  exact signedKey_eq_iff W pairs (ProducedRank.selectedMatrix C D js) hy
    (fun j i=>(hp j i).1) (fun j i=>(hp j i).2) x y

theorem producedHead_kernel {base : LeafHeadSetupProgram.Data} {n N D B z : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {table : HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHead base n N D rows low Rel B z table)
    (C : ℕ → ℕ → ℤ)
    (hrel : ∀ j v p,j < D→v∈LeafHeadSetupProgram.selectedHeads n rows low z→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v) :
    ∃ ys, table=⟨LeafHeadSetupProgram.selectedMask n rows low z,
      LeafHeadSetupProgram.selectedContext n N rows z,
      actualBuckets (base.stacks 141) ys (LeafHeadSetupProgram.selectedHeads n rows low z)
        n (LeafHeadSetupProgram.selectedHeads n rows low z).length⟩ ∧
      KeyKernel C D (LeafHeadSetupProgram.selectedHeads n rows low z) (base.stacks 141) ys := by
  obtain ⟨matrixRows,ys,hr,hy,ht⟩ := hp
  exact ⟨ys,ht,matrix_keyKernel _ C hr hy hrel⟩

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

theorem producedHead_literal_kernel {r Q D n : ℕ}
    {base : LeafHeadSetupProgram.Data} {N B z : ℕ}
    {rows : List (List Bool)} {low : List Bool}
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hps : ∀ i,(ps i).1=(owner i).val) (H : ℕ)
    {table : HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHead base n N D rows low
      (ProducedRank.FiberRel (List.ofFn ps) (ProducedRank.entryNat P A R t) H) B z table)
    (hW : H ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    ∃ ys, table=⟨LeafHeadSetupProgram.selectedMask n rows low z,
      LeafHeadSetupProgram.selectedContext n N rows z,
      actualBuckets (base.stacks 141) ys (LeafHeadSetupProgram.selectedHeads n rows low z)
        n (LeafHeadSetupProgram.selectedHeads n rows low z).length⟩ ∧
      KeyKernel (LayoutProducedMatrix.literalNat P owner A R t) D
        (LeafHeadSetupProgram.selectedHeads n rows low z) (base.stacks 141) ys := by
  apply producedHead_kernel hp
  intro j v p hj hv hr
  have hvn : v < n := HeadIdentifierProgram.chosenIds_bound _ _ _ hv
  have he := ProducedRank.fiberRel_realizes P owner A R t ps hps H j v p hj hvn hr
  refine ⟨?_,he.1⟩
  have hm := hr.2
  unfold RowSelectionProgram.pairTotal at hm
  omega

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end OAI.Algorithms
