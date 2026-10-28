import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputPackingTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankProvenance
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsEnumeration

namespace OAI.Algorithms

/-! Lookup and label provenance for the actual ambient-offset plan records.
The lemmas apply to any exact list lookup, including the first matching plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes PackingCallerProgram

 theorem addressed_raw_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    (Semantics.nativeEntries scopes mask).get (addressedIndex scopes n mask i) = (j,f) := by
  rw [addressedEntries_get] at hget
  have h1 := congrArg Prod.fst hget
  have h2 := congrArg Prod.snd hget
  apply Prod.ext
  · exact h1
  · exact Nat.add_left_cancel h2

 theorem addressed_owner_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    (Semantics.owner scopes n mask hm (addressedIndex scopes n mask i)).val = j :=
  congrArg Prod.fst (addressed_raw_of_get scopes n mask i j f hget)

 theorem addressed_factor_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    (Semantics.factor scopes n mask hm (addressedIndex scopes n mask i)).val = f :=
  congrArg Prod.snd (addressed_raw_of_get scopes n mask i j f hget)

 theorem native_entry_owner_low (scopes : List (List ℕ)) (mask : List Bool)
    (p : ℕ × ℕ) (hp : p ∈ Semantics.nativeEntries scopes mask) :
    p.1 < mask.length ∧ mask.getD p.1 false = false := by
  have h := LeafStatisticsSemantics.entries_owner_low scopes mask 0 scopes.length p.1 p.2 hp
  obtain ⟨k,hk,hb⟩ := (LeafStatisticsSemantics.lowOwners_mem 0 p.1 mask).mp h
  have he : k.val = p.1 := by simpa only [Nat.zero_add] using hk
  refine ⟨he ▸ k.isLt,?_⟩
  rw [← he,List.getD_eq_getElem _ _ k.isLt]
  exact hb

 theorem addressed_owner_low (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) :
    ((addressedEntries scopes n mask).get i).1 < mask.length ∧
      mask.getD ((addressedEntries scopes n mask).get i).1 false = false := by
  rw [addressedEntries_get]
  exact native_entry_owner_low scopes mask
    ((Semantics.nativeEntries scopes mask).get (addressedIndex scopes n mask i)) (List.get_mem _ _)

 theorem addressed_owner_low_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    j < mask.length ∧ mask.getD j false = false := by
  simpa only [hget] using addressed_owner_low scopes n mask i

@[simp] theorem addressedPacking_head (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).head =
      ProducedQueryRank.words p a tail
        (.inl (ProducedQueryRank.owner p (addressedIndex p.scopes p.n p.mask i))) := by
  rw [addressedPacking_label]
  rfl

@[simp] theorem addressedPacking_slot (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).slot 0 =
      ProducedQueryRank.words p a tail
        (.inr (ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i))) := by
  rw [addressedPacking_label]
  rfl

 theorem addressedPacking_slot_of_get (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length)
    (j : ℕ) (f : Fin p.factors)
    (hget : (addressedEntries p.scopes p.n p.mask).get i = (j,p.n+f.val)) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).slot 0 =
      ProducedQueryRank.words p a tail (.inr f) := by
  rw [addressedPacking_slot]
  have he : ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i) = f :=
    Fin.ext (addressed_factor_of_get p.scopes p.n p.mask p.mask_le i j f.val hget)
  rw [he]

 theorem addressedPacking_head_of_get (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length)
    (j : Fin p.n) (f : ℕ)
    (hget : (addressedEntries p.scopes p.n p.mask).get i = (j.val,p.n+f)) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).head =
      ProducedQueryRank.words p a tail (.inl j) := by
  rw [addressedPacking_head]
  have he : ProducedQueryRank.owner p (addressedIndex p.scopes p.n p.mask i) = j :=
    Fin.ext (addressed_owner_of_get p.scopes p.n p.mask p.mask_le i j.val f hget)
  rw [he]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
