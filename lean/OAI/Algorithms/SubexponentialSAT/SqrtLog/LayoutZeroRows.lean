import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank

namespace OAI.Algorithms

/-! A physical row table may enumerate every incidence, putting zero rows
where no constraint is present.  Such padding changes neither rank nor
exact integer buckets. -/
namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] [Fintype V] in
theorem rationalRowSpan_of_row_occurs (C : J → V → ℤ) (A : K → V → ℤ)
    (h : ∀ j, ∃ k, A k = C j) : RationalRowSpan C A := by
  classical
  intro j
  obtain ⟨k,hk⟩ := h j
  refine ⟨Pi.single k 1, ?_⟩
  intro v
  simp [Pi.single_apply, hk]

omit [Fintype K] [Fintype V] in
theorem rationalRowSpan_of_zero_or_row (C : J → V → ℤ) (A : K → V → ℤ)
    (h : ∀ k, A k = 0 ∨ ∃ j, A k = C j) : RationalRowSpan A C := by
  classical
  intro k
  rcases h k with hk | ⟨j,hj⟩
  · exact ⟨0, by intro v; simp [hk]⟩
  · refine ⟨Pi.single j 1, ?_⟩
    intro v
    simp [Pi.single_apply, hj]

omit [Fintype J] [Fintype K] in
theorem zero_extension_signature_eq_iff (C : J → V → ℤ) (A : K → V → ℤ)
    (hcover : ∀ j, ∃ k, A k = C j)
    (hshape : ∀ k, A k = 0 ∨ ∃ j, A k = C j) (x y : V → ℤ) :
    signature A x = signature A y ↔ signature C x = signature C y := by
  constructor
  · intro h
    funext j
    obtain ⟨k,hk⟩ := hcover j
    simpa only [signature, hk] using congrFun h k
  · intro h
    funext k
    rcases hshape k with hk | ⟨j,hj⟩
    · simp [signature, hk]
    · simpa only [signature, hj] using congrFun h j

omit [Fintype J] [Fintype K] [Fintype V] in
theorem zero_extension_bound (C : J → V → ℤ) (A : K → V → ℤ)
    (hshape : ∀ k, A k = 0 ∨ ∃ j, A k = C j) (W : ℕ)
    (hC : ∀ j v, |C j v| ≤ (W : ℤ)) :
    ∀ k v, |A k v| ≤ (W : ℤ) := by
  intro k v
  rcases hshape k with hk | ⟨j,hj⟩
  · simp [hk]
  · simpa only [hj] using hC j v

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open LayoutExactBuckets LayoutRowSelection

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] [Fintype V] in
theorem rowSpace_le_of_rationalRowSpan (C : J → V → ℤ) (A : K → V → ℤ)
    (hspan : RationalRowSpan C A) : rowSpace C ≤ rowSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨c,hc⟩ := hspan j
  apply (Submodule.mem_span_range_iff_exists_fun ℚ).2
  refine ⟨c, ?_⟩
  funext v
  simpa [rationalRows] using (hc v).symm

omit [Fintype V] in
theorem rowRank_zero_extension (C : J → V → ℤ) (A : K → V → ℤ)
    (hcover : ∀ j, ∃ k, A k = C j)
    (hshape : ∀ k, A k = 0 ∨ ∃ j, A k = C j) : rowRank A = rowRank C := by
  have h1 := rowSpace_le_of_rationalRowSpan C A
    (rationalRowSpan_of_row_occurs C A hcover)
  have h2 := rowSpace_le_of_rationalRowSpan A C
    (rationalRowSpan_of_zero_or_row C A hshape)
  have he : rowSpace A = rowSpace C := le_antisymm h2 h1
  unfold rowRank
  rw [he]

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
