import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalParameterCharts

/-! # Nonunit Parameter Shift -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NonunitParameterShift

noncomputable section

/-! At an infinite parameter point, the inverse coordinate is a nonunit.
Every scalar translate therefore still has a regular inverse. -/

theorem inverse (R K : Type*) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    (g : K) (hg : g ≠ 0) (a b : R) (hb : algebraMap R K b = g⁻¹)
    (hbu : ¬ IsUnit b) :
    ∃ u : R, algebraMap R K u = (g - algebraMap R K a)⁻¹ := by
  have hnu : a * b ∈ nonunits R := fun hunit => hbu (isUnit_of_mul_isUnit_right hunit)
  obtain ⟨v, hv⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (a * b) hnu
  refine ⟨b * (v⁻¹ : Rˣ), ?_⟩
  have hvK : algebraMap R K (v : R) = 1 - algebraMap R K a * g⁻¹ := by
    rw [hv, map_sub, map_one, map_mul, hb]
  have hprod : (g - algebraMap R K a) * algebraMap R K b = algebraMap R K (v : R) := by
    rw [hb, hvK, sub_mul, mul_inv_cancel₀ hg]
  have he : (g - algebraMap R K a) * algebraMap R K (b * (v⁻¹ : Rˣ)) = 1 := by
    rw [map_mul, map_units_inv, ← mul_assoc, hprod,
      mul_inv_cancel₀ ((v.isUnit.map (algebraMap R K)).ne_zero)]
  exact (inv_eq_of_mul_eq_one_right he).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NonunitParameterShift
