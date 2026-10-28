import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule

/-! # Sequence Flat Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFlatBaseChange

noncomputable section

/-! Flat base change preserves weak regularity of the actual parameter
list. At a local point containing the parameters this gives a regular
sequence over the new local ring. -/

universe u v

open RingTheory.Sequence

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S] [Module.Flat R S]

theorem weakly_regular (rs : List R) (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  have ht : IsWeaklyRegular (TensorProduct R S R) rs := h.isWeaklyRegular_lTensor
  have hs : IsWeaklyRegular S rs := (TensorProduct.rid R S).isWeaklyRegular_congr rs |>.mp ht
  exact (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hs

theorem regular [IsLocalRing S] (rs : List R) (h : IsWeaklyRegular R rs)
    (hm : ∀ r ∈ rs, algebraMap R S r ∈ IsLocalRing.maximalIdeal S) :
    IsRegular S (rs.map (algebraMap R S)) := by
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal S _ (weakly_regular R S rs h)
  intro s hs
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  exact hm r hr

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFlatBaseChange
