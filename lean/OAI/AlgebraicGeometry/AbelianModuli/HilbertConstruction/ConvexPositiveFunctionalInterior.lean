import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexSeparation

/-! # Convex Positive Functional Interior -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexPositiveFunctionalInterior

noncomputable section

/-! Strict positivity on some generator for every nonzero functional
puts zero in the interior of a full-dimensional convex hull. -/
universe u v
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module ℝ E] [ContinuousSMul ℝ E]
variable {ι : Type v}

theorem zero_mem_interior_convexHull_of_positive_functionals (v : ι → E)
    (hint : (interior (convexHull ℝ (Set.range v))).Nonempty)
    (hpos : ∀ f : StrongDual ℝ E, f ≠ 0 → ∃ i, 0 < f (v i)) :
    (0 : E) ∈ interior (convexHull ℝ (Set.range v)) := by
  by_contra hzero
  obtain ⟨f, hf, hsep⟩ := ConvexSeparation.separateConvexSetAtExteriorPoint
    (convex_convexHull ℝ (Set.range v)) hzero hint
  obtain ⟨i, hi⟩ := hpos f hf
  have hle := hsep (v i) (subset_convexHull ℝ (Set.range v) (Set.mem_range_self i))
  rw [map_zero] at hle
  exact (not_lt_of_ge hle) hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexPositiveFunctionalInterior
