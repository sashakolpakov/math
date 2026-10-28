import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramTyped
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets

/-! The selected variable IDs give a canonical order on a typed free head. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

noncomputable section

def idOrder {n : ℕ} (js : List ℕ) (hb : ∀ v ∈ js, v < n)
    (i : Fin js.length) : Fin n :=
  ⟨js.get i, hb _ (List.get_mem ..)⟩

theorem idOrder_injective {n : ℕ} (js : List ℕ) (hb : ∀ v ∈ js, v < n)
    (hn : js.Nodup) : Function.Injective (idOrder js hb) := by
  intro i j he
  exact List.nodup_iff_injective_get.mp hn (congrArg Fin.val he)

theorem idOrder_ids {n : ℕ} (js : List ℕ) (hb : ∀ v ∈ js, v < n) :
    HeadScatterProgram.headIds (idOrder js hb) = js := by
  simp [HeadScatterProgram.headIds, idOrder, List.get_eq_getElem]

variable {n r : ℕ} (H : Finset (Fin n))
  (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
  (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
  (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)

def freeOrderFun (i : Fin js.length) : Moments.Head head g := by
  let v := idOrder js hb i
  have hv : v.val ∈ js := List.get_mem ..
  let witness := (hs v).mp hv
  exact ⟨⟨v, witness.choose⟩, witness.choose_spec⟩

theorem freeOrderFun_val (i : Fin js.length) :
    (freeOrderFun H head g js hb hs i).val.val = idOrder js hb i := by
  rfl

def freeOrder : Fin js.length ≃ Moments.Head head g :=
  Equiv.ofBijective (freeOrderFun H head g js hb hs) (by
    constructor
    · intro i j he
      apply idOrder_injective js hb hn
      simpa only [freeOrderFun_val] using
        congrArg (fun x : Moments.Head head g => x.val.val) he
    · intro v
      have hv : v.val.val.val ∈ js :=
        (hs v.val.val).mpr ⟨v.val.property, v.property⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Fin.ext
      simpa only [freeOrderFun_val, idOrder] using hi)

def freeAssignmentEquiv : (Moments.Head head g → Bool) ≃ (Fin js.length → Bool) where
  toFun a i := a (freeOrder H head g js hb hn hs i)
  invFun x v := x ((freeOrder H head g js hb hn hs).symm v)
  left_inv a := by funext v; simp
  right_inv x := by funext i; simp

end

end OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
