import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramRepresentative

namespace OAI.Algorithms

/-! A tuple's physically assembled baseline agrees with each chosen head's
representative on that head when the head masks are disjoint. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput)

def assembled {α : Type*} {n : ℕ} (heads : List α)
    (mask value : α → Fin n → Bool) (baseline : Fin n → Bool) : Fin n → Bool :=
  heads.foldl (fun acc h i => if mask h i then value h i else acc i) baseline

theorem assembled_keep {α : Type*} {n : ℕ} (heads : List α)
    (mask value : α → Fin n → Bool) (baseline : Fin n → Bool) (i : Fin n) (v : Bool)
    (hw : ∀ h∈heads,mask h i=true → value h i=v) (hb : baseline i=v) :
    assembled heads mask value baseline i=v := by
  induction heads generalizing baseline with
  | nil => exact hb
  | cons h hs ih =>
      apply ih _ (fun a ha => hw a (by simp [ha]))
      cases hm : mask h i
      · simpa [hm] using hb
      · simpa [hm] using hw h (by simp) hm

theorem assembled_hit {α : Type*} {n : ℕ} (heads : List α)
    (mask value : α → Fin n → Bool) (baseline : Fin n → Bool) (i : Fin n) (v : Bool)
    (hw : ∀ h∈heads,mask h i=true → value h i=v)
    (hit : ∃ h∈heads,mask h i=true) : assembled heads mask value baseline i=v := by
  induction heads generalizing baseline with
  | nil => simp at hit
  | cons h hs ih =>
      change assembled hs mask value (fun j=>if mask h j then value h j else baseline j) i=v
      cases hm : mask h i
      · apply ih _ (fun a ha => hw a (by simp [ha]))
        obtain ⟨a,ha,hat⟩ := hit
        refine ⟨a,?_,hat⟩
        rcases List.mem_cons.mp ha with rfl|ha
        · simp [hm] at hat
        · exact ha
      · apply assembled_keep hs mask value _ i v (fun a ha=>hw a (by simp [ha]))
        simpa [hm] using hw h (by simp) hm

/-- Pointwise disjointness is enough; repeated occurrences of the same head
also preserve its representative, because they write the same value. -/
theorem assembled_on_head {α : Type*} {n : ℕ} (heads : List α)
    (mask value : α → Fin n → Bool) (baseline : Fin n → Bool)
    (head : α) (hhead : head∈heads) (i : Fin n) (hi : mask head i=true)
    (hd : ∀ other∈heads,other≠head → mask other i=false) :
    assembled heads mask value baseline i=value head i := by
  classical
  apply assembled_hit heads mask value baseline i (value head i)
  · intro other ho hot
    by_cases he : other=head
    · simp [he]
    · rw [hd other ho he] at hot
      contradiction
  · exact ⟨head,hhead,hi⟩

/-- The actual output bit at any coordinate in a chosen head equals the first
stored assignment of that head's attained bucket. -/
theorem representative_on_head {n : ℕ} (heads : List HeadInput)
    (mask value : HeadInput → Fin n → Bool) (baseline : Fin n → Bool)
    (hm : ∀ h∈heads,h.mask=List.ofFn (mask h))
    (hv : ∀ h∈heads,h.assignments.headD []=List.ofFn (value h))
    (head : HeadInput) (hhead : head∈heads) (i : Fin n) (hi : mask head i=true)
    (hd : ∀ other∈heads,other≠head → mask other i=false) :
    (representative heads (List.ofFn baseline))[i.val]?=some (value head i) := by
  rw [representative_ofFn heads mask value baseline hm hv]
  have hh := assembled_on_head heads mask value baseline head hhead i hi hd
  change assembled heads mask value baseline i=value head i at hh
  simpa [List.getElem?_ofFn,i.isLt,assembled] using congrArg some hh

/-- Coordinates belonging to no head retain the supplied baseline bit; in the
native finalizer that bit is false from the paid shape-to-zero preparation. -/
theorem assembled_outside {α : Type*} {n : ℕ} (heads : List α)
    (mask value : α → Fin n → Bool) (baseline : Fin n → Bool) (i : Fin n)
    (hi : ∀ h∈heads,mask h i=false) : assembled heads mask value baseline i=baseline i := by
  apply assembled_keep heads mask value baseline i (baseline i)
  · intro h hh ht
    rw [hi h hh] at ht
    contradiction
  · rfl

theorem representative_outside {n : ℕ} (heads : List HeadInput)
    (mask value : HeadInput → Fin n → Bool) (baseline : Fin n → Bool)
    (hm : ∀ h∈heads,h.mask=List.ofFn (mask h))
    (hv : ∀ h∈heads,h.assignments.headD []=List.ofFn (value h))
    (i : Fin n) (hi : ∀ h∈heads,mask h i=false) :
    (representative heads (List.ofFn baseline))[i.val]?=some (baseline i) := by
  rw [representative_ofFn heads mask value baseline hm hv]
  have hh := assembled_outside heads mask value baseline i hi
  simpa [List.getElem?_ofFn,i.isLt,assembled] using congrArg some hh

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

end OAI.Algorithms
