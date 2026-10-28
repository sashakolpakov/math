import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField
import OAI.AlgebraicGeometry.ComplexMultiplication.ClassDescent
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults

/-! # Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Descent.CM.Construction

noncomputable section

/-! Scalar-trace descent followed by the ordinary Lefschetz (1,1) input.
This is the coefficient-descent step needed for unchanged slots in CMReduction.
The supplied ScalarDescent proposition is a named input, never a statement stub. -/

open scoped TensorProduct

def ScalarDescentInput : Prop :=
  ∀ (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (V : Type) [AddCommGroup V] [Module ℚ V]
    (Hpq : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (t : K ⊗[ℚ] V)
    (_hconj : ∀ σ : K ≃ₐ[ℚ] K,
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ t) ∈ Hpq),
    t ∈ Submodule.span K
      {y : K ⊗[ℚ] V | ∃ v : V,
        y = (1 : K) ⊗ₜ[ℚ] v ∧ (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq}

theorem rational_algebraic_complex_inclusion (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (a : X.rationalCohomology (p + p))
    (ha : a ∈ X.geometricAlgebraicClasses p) :
    X.rationalCohomologyInclusion (p + p) a ∈
      X.complexGeometricAlgebraicClasses p := by
  have hmem : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) (p + p)
      ((1 : ℂ) ⊗ₜ[ℚ] a) ∈ X.complexGeometricAlgebraicClasses p :=
    Submodule.mem_map.mpr
      ⟨(1 : ℂ) ⊗ₜ[ℚ] a, Submodule.tmul_mem_baseChange_of_mem 1 ha, rfl⟩
  simpa only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! hmem

/-- An algebraic-coefficient degree-two tensor all of whose scalar
conjugates have type (1,1) belongs to the actual complex cycle-class span. -/
theorem degreeTwo_algebraic_of_scalar_conjugates
    (h_ScalarDescent : ScalarDescentInput) (h_DegreeTwo : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (t : K ⊗[ℚ] X.rationalCohomology 2)
    (hconj : ∀ σ : K ≃ₐ[ℚ] K,
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 2
        (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K (X.rationalCohomology 2)
          (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K (X.rationalCohomology 2) σ t)) ∈
        X.pureBettiSubspace 1 1) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 2
      (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K (X.rationalCohomology 2) t) ∈
        X.complexGeometricAlgebraicClasses 1 := by
  let Hpq := (X.pureBettiSubspace 1 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 2)
  have ht := h_ScalarDescent K (X.rationalCohomology 2) Hpq t hconj
  clear hconj
  induction ht using Submodule.span_induction with
  | mem t ht =>
      obtain ⟨a, rfl, ha⟩ := ht
      have haH : a ∈ X.rationalHodgeClasses 1 := by
        change X.rationalCohomologyInclusion 2 a ∈ X.pureBettiSubspace 1 1
        simpa only [Hpq, Submodule.mem_comap,
          ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! ha
      simpa only [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, IntermediateField.coe_one,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using!
        rational_algebraic_complex_inclusion X 1 a (h_DegreeTwo X haH)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy =>
      simpa only [map_add] using (X.complexGeometricAlgebraicClasses 1).add_mem hx hy
  | smul a x _ hx =>
      simpa only [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_smul, map_smul] using
        (X.complexGeometricAlgebraicClasses 1).smul_mem (a : ℂ) hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Descent.CM.Construction
