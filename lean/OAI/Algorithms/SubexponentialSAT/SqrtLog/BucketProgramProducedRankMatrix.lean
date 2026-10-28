import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramRank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramCompatibility
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSource

namespace OAI.Algorithms

/-! The exact row-major matrix emitted by the entry scanner, in the actual
selected identifier order. These proofs introduce no runtime permutation. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

private theorem forall₂_typed {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (hr : List.Forall₂ R xs ys) :
    ∃ f : Fin xs.length → β, ys=List.ofFn f ∧ ∀ i,R (xs.get i) (f i) := by
  have hlen := hr.length_eq
  let f : Fin xs.length → β := fun i=>ys.get ⟨i.val,by rw [←hlen]; exact i.isLt⟩
  refine ⟨f,?_,?_⟩
  · apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp [f]
  · intro i
    have hh := hr.get (i:=i.val) i.isLt (by rw [←hlen]; exact i.isLt)
    simpa [f,List.get_eq_getElem] using hh

/-- Every physical pair retains its original row number and selected ID. -/
theorem matrixRel_typed {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    ∃ pairs : Fin D → Fin js.length → SignedWord,
      rows=List.ofFn (fun j=>List.ofFn (pairs j)) ∧
      ∀ j i,Rel j.val (js.get i) (pairs j i) ∧ LayoutMatrixProgram.pairLength (pairs j i) ≤ B := by
  classical
  have hr' : List.Forall₂ (fun j row=>List.Forall₂
      (fun v p=>Rel j v p ∧ LayoutMatrixProgram.pairLength p ≤ B) js row)
      (List.ofFn (fun j : Fin D=>j.val)) rows := by
    have he : List.ofFn (fun j : Fin D=>j.val)=List.range D := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp
    rw [he]
    exact hr
  obtain ⟨rr,hrr,hh⟩ := forall₂_typed hr'
  have hl : (List.ofFn (fun j : Fin D=>j.val)).length=D := by simp
  let rr' : Fin D → List LayoutMatrixProgram.Pair := fun j=>rr (Fin.cast hl.symm j)
  have he : rows=List.ofFn rr' := by simpa [rr'] using hrr
  have hrow (j : Fin D) : List.Forall₂
      (fun v p=>Rel j.val v p ∧ LayoutMatrixProgram.pairLength p ≤ B) js (rr' j) := by
    simpa [rr'] using hh (Fin.cast hl.symm j)
  have hx : ∀ j,∃ f : Fin js.length → LayoutMatrixProgram.Pair,
      rr' j=List.ofFn f ∧ ∀ i,Rel j.val (js.get i) (f i) ∧ LayoutMatrixProgram.pairLength (f i) ≤ B :=
    fun j=>forall₂_typed (hrow j)
  choose pairs hp hv using hx
  refine ⟨pairs,?_,hv⟩
  exact he.trans (congrArg List.ofFn (funext hp))

/-- The coefficient matrix uses exactly the scanner's selected-ID order. -/
def selectedMatrix (C : ℕ → ℕ → ℤ) (D : ℕ) (js : List ℕ) : Fin D → Fin js.length → ℤ :=
  fun j i=>C j.val (js.get i)

/-- Exact cardinality of the actual output buckets, derived from the original
entry relation and the physical preprocessing relation. -/
theorem actualBuckets_length_le_rank
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B D : ℕ}
    {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (W : List Bool) {ys : List (List (List Bool))} (n H : ℕ) (C : ℕ → ℕ → ℤ)
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows)
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W)) rows ys)
    (hrel : ∀ j v p,j < D→v∈js→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v)
    (hbound : ∀ j v p,j < D→v∈js→Rel j v p→|C j v| ≤ (H:ℤ)) :
    (BucketTupleProgram.actualBuckets W ys js n js.length).length ≤
      (2*js.length*H+1)^LayoutRank.rowRank (selectedMatrix C D js) := by
  obtain ⟨pairs,rfl,hpairs⟩ := matrixRel_typed hr
  have hn (j : Fin D) (i : Fin js.length) :=
    hrel j.val (js.get i) (pairs j i) j.isLt (List.get_mem ..) (hpairs j i).1
  have hb (j : Fin D) (i : Fin js.length) : |selectedMatrix C D js j i| ≤ (H:ℤ) :=
    hbound j.val (js.get i) (pairs j i) j.isLt (List.get_mem ..) (hpairs j i).1
  have ht := storedTable_length_le_rank W pairs (selectedMatrix C D js) js n H hy
    (fun j i=>(hn j i).1) (fun j i=>(hn j i).2) hb
  simpa only [BucketTupleProgram.actualBuckets,BucketTupleProgram.controllerBuckets,
    SubexponentialSAT.Subexp.PackingBucketTable.table,List.length_map,Controller.labelledRecords,
    Controller.keys] using ht

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end OAI.Algorithms
