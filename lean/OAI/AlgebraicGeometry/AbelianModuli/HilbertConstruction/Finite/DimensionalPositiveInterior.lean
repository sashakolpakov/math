import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConvexPositiveFunctionalInterior
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasisInteriorWitness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Dimensional Positive Interior -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.DimensionalPositiveInterior

noncomputable section

/-! In finite dimensions, positivity on some generator for every
nonzero linear functional already forces a full-dimensional convex hull
and puts zero in its interior. -/
open scoped Classical
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type v} [Nonempty ι]

theorem affineSpan_eq_top_of_positive_functionals (v : ι → E)
    (hpos : ∀ f : StrongDual ℝ E, f ≠ 0 → ∃ i, 0 < f (v i)) :
    affineSpan ℝ (Set.range v) = ⊤ := by
  let S := affineSpan ℝ (Set.range v)
  let i₀ : ι := Classical.choice inferInstance
  have hmem (i : ι) : v i ∈ S := subset_affineSpan ℝ (Set.range v) (Set.mem_range_self i)
  by_contra hS
  have hd : S.direction ≠ ⊤ := fun he => hS
    ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨v i₀, hmem i₀⟩).mp he)
  obtain ⟨φ, hφ, hker⟩ := S.direction.exists_le_ker_of_lt_top hd.lt_top
  let f : StrongDual ℝ E := φ.toContinuousLinearMap
  have hf : f ≠ 0 := fun h => hφ (congrArg ContinuousLinearMap.toLinearMap h)
  have hconst (i : ι) : f (v i) = f (v i₀) := by
    have hh := hker (AffineSubspace.vsub_mem_direction (hmem i) (hmem i₀))
    change φ (v i - v i₀) = 0 at hh
    rw [map_sub] at hh
    exact sub_eq_zero.mp hh
  obtain ⟨i, hi⟩ := hpos f hf
  obtain ⟨j, hj⟩ := hpos (-f) (neg_ne_zero.mpr hf)
  change 0 < -f (v j) at hj
  rw [hconst i] at hi
  rw [hconst j] at hj
  exact (not_lt_of_ge hi.le) (neg_pos.mp hj)

theorem zero_mem_interior_convexHull_of_all_positive_functionals (v : ι → E)
    (hpos : ∀ f : StrongDual ℝ E, f ≠ 0 → ∃ i, 0 < f (v i)) :
    (0 : E) ∈ interior (convexHull ℝ (Set.range v)) :=
  ConvexPositiveFunctionalInterior.zero_mem_interior_convexHull_of_positive_functionals v
    (Affine.BasisInteriorWitness.convexHull_interior_nonempty_of_affineSpan_eq_top
      (affineSpan_eq_top_of_positive_functionals v hpos)) hpos

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.DimensionalPositiveInterior
