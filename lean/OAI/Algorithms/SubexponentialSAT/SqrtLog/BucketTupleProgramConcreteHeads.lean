import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteFinite
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramCoverage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramHeadOrder

namespace OAI.Algorithms

/-! The actual selected-ID order is a bijection with the typed free head.
Scattered ambient words and their raw keys are transported along this order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open BucketProgram

def orderedModel {A : Type*} {n h : ℕ} (head : Fin h → Fin n)
    (hinj : Function.Injective head) (js : List ℕ) (hids : HeadScatterProgram.headIds head=js)
    (W : List Bool) (ys : List (List (List Bool))) (e : A ≃ (Fin h → Bool)) :
    RecordModel A (Controller.labelledRecords W ys js n h) where
  label a := Label.key W (List.ofFn (e a)) ys
  encode a := HeadScatterProgram.mask n js (List.ofFn (e a))
  encode_injective := by
    intro a b he
    apply e.injective
    rw [←hids] at he
    exact HeadScatterProgram.typed_mask_injective head hinj he
  payloads_nodup := by
    simpa only [Controller.labelledRecords,hids] using labelled_payloads_nodup head hinj W ys
  mem_iff := by
    intro key word
    constructor
    · intro hm
      obtain ⟨bits,hbits,he⟩ := List.mem_map.mp hm
      obtain ⟨x,rfl⟩ := assignments_sound hbits
      refine ⟨e.symm x,?_,?_⟩
      · simpa using congrArg Prod.fst he
      · simpa using congrArg Prod.snd he
    · rintro ⟨a,ha,hb⟩
      exact List.mem_map.mpr ⟨List.ofFn (e a),assignments_complete (e a),Prod.ext ha hb⟩

variable {n r : ℕ} (H : Finset (Fin n))
  (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
  (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
  (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)

def freeModel (W : List Bool) (ys : List (List (List Bool))) :
    RecordModel (Moments.Head head g → Bool) (Controller.labelledRecords W ys js n js.length) :=
  orderedModel (idOrder js hb) (idOrder_injective js hb hn) js (idOrder_ids js hb) W ys
    (freeAssignmentEquiv H head g js hb hn hs)

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
