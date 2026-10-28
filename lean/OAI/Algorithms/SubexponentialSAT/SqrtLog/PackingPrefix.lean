import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIdentity
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentEnumeration

namespace OAI.Algorithms

/-! Heads-first numbering and the actual reverse-list assignment prefix. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Enumeration
variable {A B R : Type*} [DecidableEq A] [DecidableEq B]

theorem indexCode_map_injective (f : A → B) (hf : Function.Injective f)
    (xs : List A) (a : A) : indexCode (xs.map f) (f a) = indexCode xs a := by
  let _ : BEq A := instBEqOfDecidableEq
  let _ : BEq B := instBEqOfDecidableEq
  unfold indexCode
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hb : (f x == f a) = (x == a) := by
      apply Bool.eq_iff_iff.mpr
      simp [hf.eq_iff]
    simp only [List.map_cons, List.idxOf_cons, hb, ih]

theorem prefix_enumeration_sum [Fintype A] [AddCommMonoid R]
    (xs : List A) (hn : xs.Nodup) (hf : ∀ x, x ∈ xs) (f : A → R) :
    (xs.map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset f hn]
  have heq : xs.toFinset = Finset.univ := by ext x; simp [hf x]
  rw [heq]
end Enumeration

section Indices
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def headsFirstIndices (vertices : List V) (factors : List E) : List (V ⊕ E) :=
  vertices.map Sum.inl ++ factors.map Sum.inr

theorem headsFirst_index_head (vertices : List V) (factors : List E)
    (v : V) (hv : v ∈ vertices) :
    indexCode (headsFirstIndices vertices factors) (.inl v) = indexCode vertices v := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  unfold headsFirstIndices indexCode
  rw [List.idxOf_append_of_mem (by simpa using hv)]
  exact indexCode_map_injective Sum.inl Sum.inl_injective vertices v

theorem headsFirst_index_factor (vertices : List V) (factors : List E) (e : E) :
    indexCode (headsFirstIndices vertices factors) (.inr e) =
      vertices.length + indexCode factors e := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  unfold headsFirstIndices indexCode
  rw [List.idxOf_append_of_notMem (by simp)]
  simp only [List.length_map]
  congr 1
  exact indexCode_map_injective (Sum.inr : E → V ⊕ E) Sum.inr_injective factors e

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_length (vertices : List V) (factors : List E) :
    (headsFirstIndices vertices factors).length = vertices.length + factors.length := by
  simp [headsFirstIndices]

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_complete (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors) :
    ∀ a, a ∈ headsFirstIndices vertices factors := by
  intro a
  cases a <;> simp [headsFirstIndices, hv, he]

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_nodup (vertices : List V) (factors : List E)
    (hv : vertices.Nodup) (he : factors.Nodup) :
    (headsFirstIndices vertices factors).Nodup := by
  simp only [headsFirstIndices, List.nodup_append]
  refine ⟨hv.map Sum.inl_injective, he.map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
  simp at hab
end Indices

section Decoding
variable {W : Type*}

theorem decode_prefix_update (default candidate : W) (fixed : List W) :
    decode default (candidate :: fixed) = Function.update (decode default fixed) fixed.length candidate := rfl

theorem decode_prefix_before (default candidate : W) (fixed : List W)
    (i : ℕ) (hi : i < fixed.length) :
    decode default (candidate :: fixed) i = fixed.reverse.getD i default := by
  rw [decode_prefix_update, Function.update_of_ne (Nat.ne_of_lt hi),
    SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD]

theorem decode_prefix_at (default candidate : W) (fixed : List W) :
    decode default (candidate :: fixed) fixed.length = candidate := by simp [decode]

theorem prefix_not_remaining (fixed : List W) (n i : ℕ) (hi : i ≤ fixed.length) :
    i ∉ List.range' (fixed.length + 1) n := by
  simp only [List.mem_range']
  omega
end Decoding

section Sums
variable {V E W R : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    [AddCommMonoid R]

theorem headsFirst_prefix_sum (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hv : ∀ v, v ∈ vertices)
    (default : W) (fixed : List W) (hprefix : fixed.length ≤ vertices.length) (F : W → R) :
    (∑ v : V, if indexCode (headsFirstIndices vertices factors) (.inl v) < fixed.length
      then F (decode default fixed (indexCode (headsFirstIndices vertices factors) (.inl v)))
      else 0) = (fixed.map F).sum := by
  simp_rw [headsFirst_index_head vertices factors _ (hv _)]
  rw [← prefix_enumeration_sum vertices hvn hv]
  let G : ℕ → R := fun i => if i < fixed.length then F (decode default fixed i) else 0
  change (vertices.map (fun v => G (indexCode vertices v))).sum = _
  have hm : vertices.map (fun v => G (indexCode vertices v)) =
      (vertices.map (indexCode vertices)).map G := by
    simp only [List.map_map, Function.comp_def]
  rw [hm, map_idxOf_eq_range vertices hvn]
  rw [← List.sum_toFinset G List.nodup_range]
  have hset : (List.range vertices.length).toFinset = Finset.range vertices.length := by
    ext i
    simp
  rw [hset]
  have hsum : (∑ i ∈ Finset.range vertices.length, G i) =
      ∑ i ∈ Finset.range fixed.length, G i := by
    symm
    apply Finset.sum_subset (Finset.range_mono hprefix)
    intro i hi hnot
    simp only [Finset.mem_range] at hnot
    simp [G, hnot]
  rw [hsum]
  simp only [G]
  have hremove : (∑ i ∈ Finset.range fixed.length,
      if i < fixed.length then F (decode default fixed i) else 0) =
      ∑ i ∈ Finset.range fixed.length, F (decode default fixed i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  rw [hremove]
  have hget : (∑ i ∈ Finset.range fixed.length, F (decode default fixed i)) =
      (fixed.reverse.map F).sum := by
    have hrev : (∑ i ∈ Finset.range fixed.reverse.length, F (fixed.reverse.getD i default)) =
        (fixed.reverse.map F).sum := by
      rw [Finset.sum_range]
      calc
        _ = ∑ i : Fin fixed.reverse.length, F fixed.reverse[i.val] := by
          apply Finset.sum_congr rfl
          intro i _
          rw [List.getD_eq_getElem _ _ i.isLt]
        _ = _ := Fin.sum_univ_fun_getElem fixed.reverse F
    simpa only [List.length_reverse, SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] using hrev
  rw [hget, List.map_reverse, List.sum_reverse]
end Sums

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
