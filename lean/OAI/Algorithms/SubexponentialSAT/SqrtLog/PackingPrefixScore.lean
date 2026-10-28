import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefix

namespace OAI.Algorithms

/-! Exact head-term enumeration and physical prefix overlap. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

private theorem prefix_sum_flatMap {A R : Type*} [AddMonoid R]
    (xs : List A) (f : A → List R) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

section Terms
variable {I V R : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid R]

def headScoreTerms (vertices : List V) (Q : ℕ) : List (ScoreTerm I V Q) :=
  (List.finRange Q).flatMap (fun t => (vertices.product vertices).map
    (fun pair => Sum.inr (t, pair.1, pair.2)))

theorem headScoreTerms_sum (vertices : List V) (hvn : vertices.Nodup)
    (hv : ∀ v, v ∈ vertices) (Q : ℕ) (F : ScoreTerm I V Q → R) :
    ((headScoreTerms vertices Q).map F).sum =
      ∑ t : Fin Q, ∑ v : V, ∑ w : V, F (.inr (t,v,w)) := by
  have hp : (vertices.product vertices).Nodup := hvn.product hvn
  have hpf : ∀ p : V × V, p ∈ vertices.product vertices := by
    intro p
    exact List.mem_product.mpr ⟨hv p.1, hv p.2⟩
  simp only [headScoreTerms, List.map_flatMap, prefix_sum_flatMap, List.map_map,
    Function.comp_def]
  simp_rw [prefix_enumeration_sum (vertices.product vertices) hp hpf]
  rw [prefix_enumeration_sum (List.finRange Q) (List.nodup_finRange Q) (by simp)]
  simp only [Fintype.sum_prod_type]
end Terms

section Prior
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {r Q : ℕ}

omit [Fintype V] in
/-- Excluding the fresh key and its future suffix retains exactly earlier head keys. -/
theorem headsFirst_prior_iff (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (p n : ℕ)
    (hsize : n + 1 + p = (headsFirstIndices vertices factors).length) (v : V) :
    ¬ (indexCode (headsFirstIndices vertices factors) (.inl v) = p ∨
      indexCode (headsFirstIndices vertices factors) (.inl v) ∈ List.range' (p+1) n) ↔
      indexCode (headsFirstIndices vertices factors) (.inl v) < p := by
  simp only [headsFirst_index_head vertices factors v (hv v)]
  have hpos : indexCode vertices v < vertices.length := List.idxOf_lt_length_iff.mpr (hv v)
  rw [headsFirst_length] at hsize
  simp only [List.mem_range'_1]
  omega

theorem priorHeadOverlap_eq_prefix (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (hv : ∀ v, v ∈ vertices)
    (default z : Word r Q) (fixed : List (Word r Q)) (n : ℕ)
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hprefix : fixed.length ≤ vertices.length) :
    (∑ t : Fin Q, ∑ v : V,
      if indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
        indexCode (headsFirstIndices vertices factors) (.inl v) ∈
          List.range' (fixed.length+1) n then 0
      else if z t = decode default fixed
        (indexCode (headsFirstIndices vertices factors) (.inl v)) t then (1 : ℕ) else 0) =
      (fixed.map (fun w => ∑ t : Fin Q, if z t = w t then (1 : ℕ) else 0)).sum := by
  have ht (t : Fin Q) : (∑ v : V,
      if indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
        indexCode (headsFirstIndices vertices factors) (.inl v) ∈
          List.range' (fixed.length+1) n then 0
      else if z t = decode default fixed
        (indexCode (headsFirstIndices vertices factors) (.inl v)) t then (1 : ℕ) else 0) =
      (fixed.map (fun w => if z t = w t then (1 : ℕ) else 0)).sum := by
    rw [← headsFirst_prefix_sum vertices factors hvn hv default fixed hprefix
      (fun w => if z t = w t then (1 : ℕ) else 0)]
    apply Finset.sum_congr rfl
    intro v _
    have hp := headsFirst_prior_iff vertices factors hv fixed.length n hsize v
    by_cases h : indexCode (headsFirstIndices vertices factors) (.inl v) = fixed.length ∨
      indexCode (headsFirstIndices vertices factors) (.inl v) ∈ List.range' (fixed.length+1) n
    · have hh : ¬ indexCode (headsFirstIndices vertices factors) (.inl v) < fixed.length := by
        intro hh; exact (hp.mpr hh) h
      simp only [ite_eq_left h, ite_eq_right hh]
    · simp only [ite_eq_right h, ite_eq_left (hp.mp h)]
  simp_rw [ht]
  have exchange (xs : List (Word r Q)) :
      (∑ t : Fin Q, (xs.map (fun w => if z t = w t then (1 : ℕ) else 0)).sum) =
        (xs.map (fun w => ∑ t : Fin Q, if z t = w t then (1 : ℕ) else 0)).sum := by
    induction xs with
    | nil => simp
    | cons w xs ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  exact exchange fixed
end Prior
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
