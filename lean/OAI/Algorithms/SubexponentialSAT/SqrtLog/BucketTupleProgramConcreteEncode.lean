import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteHeads
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteKernel

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open BucketProgram
open scoped BigOperators

variable {n r : ℕ} (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r) (g : Fin r)
  (js : List ℕ) (hb : ∀ v∈js,v < n) (hn : js.Nodup)
  (hs : ∀ v : Fin n,v.val∈js ↔ ∃ hv : v∉H,head ⟨v,hv⟩=g)

theorem freeOrder_apply_val (i : Fin js.length) :
    (freeOrder H head g js hb hn hs i).val.val=idOrder js hb i := rfl

def ambientEncode (a : Moments.Head head g → Bool) : List Bool :=
  List.ofFn (fun v : Fin n=>if hv : v∉H then
    if hg : head ⟨v,hv⟩=g then a ⟨⟨v,hv⟩,hg⟩ else false else false)

theorem freeModel_encode_head (W : List Bool) (ys : List (List (List Bool)))
    (a : Moments.Head head g → Bool) (v : Moments.Head head g) :
    ((freeModel H head g js hb hn hs W ys).encode a)[v.val.val.val]?=some (a v) := by
  let e := freeOrder H head g js hb hn hs
  let i := e.symm v
  have hiv : idOrder js hb i=v.val.val := by
    simpa only [e,freeOrder_apply_val] using congrArg (fun z : Moments.Head head g=>z.val.val)
      (e.apply_symm_apply v)
  have hm := HeadScatterProgram.typed_mask_head (idOrder js hb) (idOrder_injective js hb hn)
    (freeAssignmentEquiv H head g js hb hn hs a) i
  rw [idOrder_ids,hiv] at hm
  simpa [freeModel,orderedModel,HeadScatterProgram.headBits,freeAssignmentEquiv,i,e] using hm

theorem ambientEncode_get (a : Moments.Head head g → Bool) (v : Fin n) :
    (ambientEncode H head g a)[v.val]? = some (if hv : v∉H then
      if hg : head ⟨v,hv⟩=g then a ⟨⟨v,hv⟩,hg⟩ else false else false) := by
  simp only [ambientEncode,List.getElem?_ofFn,dite_eq_left v.isLt]

theorem freeModel_encode (W : List Bool) (ys : List (List (List Bool)))
    (a : Moments.Head head g → Bool) :
    (freeModel H head g js hb hn hs W ys).encode a=ambientEncode H head g a := by
  change HeadScatterProgram.mask n js
    (List.ofFn (freeAssignmentEquiv H head g js hb hn hs a))=ambientEncode H head g a
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · let v : Fin n := ⟨j,hj⟩
    have he := ambientEncode_get H head g a v
    change (ambientEncode H head g a)[j]? = _ at he
    rw [he]
    by_cases hv : v∉H
    · rw [dite_eq_left hv]
      by_cases hg : head ⟨v,hv⟩=g
      · rw [dite_eq_left hg]
        exact freeModel_encode_head H head g js hb hn hs W ys a ⟨⟨v,hv⟩,hg⟩
      · rw [dite_eq_right hg]
        have hnot : j∉js := by
          intro hm
          obtain ⟨hv',hh⟩ := (hs v).mp hm
          exact hg hh
        exact HeadScatterProgram.mask_outside n js _ j hb hj hnot
    · rw [dite_eq_right hv]
      have hnot : j∉js := by
        intro hm
        obtain ⟨hv',hh⟩ := (hs v).mp hm
        exact hv hv'
      exact HeadScatterProgram.mask_outside n js _ j hb hj hnot
  · have hlen : (HeadScatterProgram.mask n js
        (List.ofFn (freeAssignmentEquiv H head g js hb hn hs a))).length=n :=
      HeadScatterProgram.mask_length n js _ hb
    rw [List.getElem?_eq_none (by omega)]
    simp only [ambientEncode,List.getElem?_ofFn,dite_eq_right hj]

theorem freeModel_key_iff {D : ℕ} (W : List Bool) (ys : List (List (List Bool)))
    (C : ℕ → ℕ → ℤ) (hk : KeyKernel C D js W ys)
    (x y : Moments.Head head g → Bool) :
    (freeModel H head g js hb hn hs W ys).label x=
        (freeModel H head g js hb hn hs W ys).label y ↔
      ∀ j : Fin D,(∑ v : Moments.Head head g,C j.val v.val.val.val*(if x v then 1 else 0))=
        (∑ v : Moments.Head head g,C j.val v.val.val.val*(if y v then 1 else 0)) := by
  have hsum (a : Moments.Head head g → Bool) (j : Fin D) :
      (∑ i : Fin js.length,C j.val (js.get i)*
        (if freeAssignmentEquiv H head g js hb hn hs a i then 1 else 0))=
      ∑ v : Moments.Head head g,C j.val v.val.val.val*(if a v then 1 else 0) := by
    change (∑ i : Fin js.length,C j.val (js.get i)*
      (if a (freeOrder H head g js hb hn hs i) then 1 else 0)) = _
    simpa only [freeOrder_apply_val,idOrder] using
      (freeOrder H head g js hb hn hs).sum_comp
        (fun v : Moments.Head head g=>C j.val v.val.val.val*(if a v then 1 else 0))
  change BucketProgram.Label.key W (List.ofFn _) ys=BucketProgram.Label.key W (List.ofFn _) ys ↔ _
  rw [hk (freeAssignmentEquiv H head g js hb hn hs x)
    (freeAssignmentEquiv H head g js hb hn hs y)]
  exact forall_congr' (fun j=>by rw [hsum x j,hsum y j])

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end
end OAI.Algorithms
