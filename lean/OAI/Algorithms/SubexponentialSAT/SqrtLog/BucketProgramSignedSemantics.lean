import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramCoverage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessBounds

namespace OAI.Algorithms

/-! A typed view of the physically produced signed-matrix preprocessing output.
The view does not compute or reorder entries: it identifies the exact list
already emitted by the primitive scanner. All supplied rows are retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

private theorem forall₂_ofFn_right_exists {α β : Type*} {d : ℕ}
    {R : α → β → Prop} (f : Fin d → α) {ys : List β}
    (hy : List.Forall₂ R (List.ofFn f) ys) :
    ∃ g : Fin d → β, ys=List.ofFn g ∧ ∀ i, R (f i) (g i) := by
  have hlen : ys.length=d := by simpa only [List.length_ofFn] using hy.length_eq.symm
  let g : Fin d → β := fun i => ys.get ⟨i.val,by rw [hlen]; exact i.isLt⟩
  refine ⟨g,?_,?_⟩
  · apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp [g]
  · intro i
    have hh := hy.get (i:=i.val) (by simp) (by rw [hlen]; exact i.isLt)
    simpa [g,List.get_eq_getElem] using hh

/-- The existential coefficients are just the already produced words at their
original row and column positions. No basis or permutation is inserted. -/
theorem shiftedMatrix_typed {h d : ℕ} (W : List Bool)
    (pairs : Fin d → Fin h → SignedWord) {ys : List (List (List Bool))}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys) :
    ∃ c : Fin d → Fin h → List Bool,
      ys=List.ofFn (fun j => List.ofFn (c j)) ∧ ∀ j i, shiftedWord W (pairs j i) (c j i) := by
  classical
  obtain ⟨rows,rfl,hr⟩ := forall₂_ofFn_right_exists (fun j => List.ofFn (pairs j)) hy
  have hx : ∀ j, ∃ c : Fin h → List Bool,
      rows j=List.ofFn c ∧ ∀ i,shiftedWord W (pairs j i) (c i) :=
    fun j => forall₂_ofFn_right_exists (pairs j) (hr j)
  choose c hc hv using hx
  exact ⟨c,congrArg List.ofFn (funext hc),hv⟩

/-- Exact bucket membership for the matrix actually emitted from signed
integer entries. The number d is the full serialized row count. -/
theorem generated_signed_bucket_exact {n h d : ℕ}
    (head : Fin h → Fin n) (hinj : Function.Injective head)
    (W : List Bool) (pairs : Fin d → Fin h → SignedWord) (A : Fin d → Fin h → ℤ)
    {ys : List (List (List Bool))}
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys)
    (hN : ∀ j i,SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W)
    (hA : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).1 : ℤ)-
      (SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 : ℤ)=A j i)
    (x y : Fin h → Bool) :
    HeadScatterProgram.mask n (HeadScatterProgram.headIds head) (List.ofFn y) ∈
      bucketAssignments (Label.labelled W ys (HeadScatterProgram.headIds head) n (assignments h))
        (Label.key W (List.ofFn x) ys) ↔
    ∀ j, (∑ i,A j i*(if x i then 1 else 0))=(∑ i,A j i*(if y i then 1 else 0)) := by
  obtain ⟨c,rfl,hc⟩ := shiftedMatrix_typed W pairs hy
  apply generated_bucket_exact head hinj W c A x y
  intro j i
  have hv := shiftedWord_integer W (pairs j i) (c j i) (hc j i) (hN j i)
  simpa only [hA j i] using hv

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
