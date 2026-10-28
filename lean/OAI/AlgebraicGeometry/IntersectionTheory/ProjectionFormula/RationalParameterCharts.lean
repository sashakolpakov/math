import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor

/-! # Rational Parameter Charts -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalParameterCharts

noncomputable section

/-! The two regular affine charts of a projective-line parameter
remain a covering after translating the parameter by a scalar. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem shift (R K : Type*) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    (g : K) (hg : g ≠ 0) (a : R)
    (h : (∃ u : R, algebraMap R K u = g) ∨ (∃ u : R, algebraMap R K u = g⁻¹)) :
    (∃ u : R, algebraMap R K u = g - algebraMap R K a) ∨
      (∃ u : R, algebraMap R K u = (g - algebraMap R K a)⁻¹) := by
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨b - a, by rw [map_sub, hb]⟩
  · by_cases hu : IsUnit b
    · obtain ⟨v, rfl⟩ := hu
      left
      refine ⟨(v⁻¹ : Rˣ) - a, ?_⟩
      rw [map_sub, map_units_inv, hb, inv_inv]
    · have hnu : a * b ∈ nonunits R := fun hunit => hu (isUnit_of_mul_isUnit_right hunit)
      obtain ⟨v, hv⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (a * b) hnu
      right
      refine ⟨b * (v⁻¹ : Rˣ), ?_⟩
      have hvK : algebraMap R K (v : R) = 1 - algebraMap R K a * g⁻¹ := by
        rw [hv, map_sub, map_one, map_mul, hb]
      have hprod : (g - algebraMap R K a) * algebraMap R K b = algebraMap R K (v : R) := by
        rw [hb, hvK, sub_mul, mul_inv_cancel₀ hg]
      have he : (g - algebraMap R K a) * algebraMap R K (b * (v⁻¹ : Rˣ)) = 1 := by
        rw [map_mul, map_units_inv, ← mul_assoc, hprod,
          mul_inv_cancel₀ ((v.isUnit.map (algebraMap R K)).ne_zero)]
      exact (inv_eq_of_mul_eq_one_right he).symm

theorem scalar_shift (Z : Scheme) [IsIntegral Z] (π : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (g : Z.functionField) (hg : g ≠ 0)
    (h : ∀ x : Z,
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g) ∨
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = g⁻¹)) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra π
    ∀ x : Z,
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u =
        g - algebraMap ℂ Z.functionField a) ∨
      (∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u =
        (g - algebraMap ℂ Z.functionField a)⁻¹) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra π
  intro x
  let := FunctionDivisor.stalkScalarAlgebra π x
  let := FunctionDivisor.stalkScalarTower π x
  have hs := shift (Z.presheaf.stalk x) Z.functionField g hg (algebraMap ℂ (Z.presheaf.stalk x) a) (h x)
  rwa [← IsScalarTower.algebraMap_apply] at hs

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RationalParameterCharts
