import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField

/-! # Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Coefficients.CM.SurfaceConstruction

noncomputable section

/-!
Coefficient-field algebraicity for SurfaceConstruction, using the actual rational geometric
cycle map. Scalar-trace descent (ScalarDescent) and degree-two algebraicity (DegreeTwo,
or Lefschetz ChernClass followed by the divisor comparison) are explicit hypotheses.
No algebraicity of the switch or of a pair tensor is assumed.
-/

open _root_.CategoryTheory
open scoped TensorProduct

/-- The actual geometric cycle map extended to the coefficient field. -/
def coefficientAlgebraicClasses (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule E (E ⊗[ℚ] X.rationalCohomology (p + p)) :=
  LinearMap.range ((X.geometricCycleClassMap p).baseChange E)

/-- Include E-valued rational cohomology in ordinary complex Betti cohomology. -/
def realizeCoefficient (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (x : E ⊗[ℚ] X.rationalCohomology n) : X.complexCohomology n :=
  ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) n
    (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E (X.rationalCohomology n) x)

@[simp]
theorem realizeCoefficient_tmul (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : E) (x : X.rationalCohomology n) :
    realizeCoefficient E X n (a ⊗ₜ[ℚ] x) =
      (a : ℂ) • X.rationalCohomologyInclusion n x := rfl

/-- Algebraic coefficient classes give exactly the finite type of
E-linear combination used by the SurfaceConstruction target. -/
theorem coefficientAlgebraicClasses_finite_sum
    (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    {x : E ⊗[ℚ] X.rationalCohomology (p + p)}
    (hx : x ∈ coefficientAlgebraicClasses E X p) :
    ∃ (n : ℕ) (a : Fin n → E) (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p),
      (∑ j : Fin n, (a j : ℂ) • X.rationalCohomologyInclusion (p + p)
        (X.geometricCycleClassMap p (Z j))) = realizeCoefficient E X (p + p) x := by
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨n, a, Z, hz⟩ := TensorProduct.exists_sum_tmul_eq z
  refine ⟨n, a, Z, ?_⟩
  rw [hz]
  simp only [realizeCoefficient, map_sum, LinearMap.baseChange_tmul,
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
  rfl

/-- Scalar conjugation changes cycle coefficients, leaving the underlying
complex variety and its algebraic cycle supports fixed. -/
theorem coefficientAlgebraicClasses_scalarConjugate
    (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (σ : Gal(E/ℚ)) {x : E ⊗[ℚ] X.rationalCohomology (p + p)}
    (hx : x ∈ coefficientAlgebraicClasses E X p) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology (p + p)) σ x ∈
      coefficientAlgebraicClasses E X p := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X p) σ z,
    (ComplexMultiplication.EmbeddingCoefficientField.CM.scalarConjugate_baseChange E σ (X.geometricCycleClassMap p) z).symm⟩

/-- A nonzero multiple of a coefficient class is algebraic precisely
when the class is; this removes the nonzero contraction coefficient. -/
theorem coefficientAlgebraicClasses_of_smul
    (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : E) (ha : a ≠ 0) (x : E ⊗[ℚ] X.rationalCohomology (p + p))
    (hx : a • x ∈ coefficientAlgebraicClasses E X p) :
    x ∈ coefficientAlgebraicClasses E X p := by
  have h := (coefficientAlgebraicClasses E X p).smul_mem a⁻¹ hx
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using h

/-- Full ScalarDescent scalar-trace descent, for an arbitrary prescribed complex
Hodge subspace and arbitrary rational vector space. -/
def ScalarTraceDescent (E : IntermediateField ℚ ℂ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V]
    (Hpq : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V)) (t : E ⊗[ℚ] V),
    (∀ σ : Gal(E/ℚ),
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion E V (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E V σ t) ∈ Hpq) →
    t ∈ Submodule.span E
      {y : E ⊗[ℚ] V | ∃ v : V,
        y = (1 : E) ⊗ₜ[ℚ] v ∧ (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq}

/-- Full geometric degree-two conclusion of DegreeTwo. -/
def DegreeTwoAlgebraicity : Prop :=
  ∀ (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : X.rationalCohomology 2),
    X.IsRationalHodgeClass 1 a →
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 1, X.geometricCycleClassMap 1 z = a

/-- Trace and Lefschetz produce an algebraic divisor class over E.
The hypothesis tests each actual scalar conjugate in ordinary Betti H^(1,1). -/
theorem degreeTwo_algebraic_of_conjugates
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E]
    (hScalarDescent : ScalarTraceDescent E) (hDegreeTwo : DegreeTwoAlgebraicity)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (t : E ⊗[ℚ] X.rationalCohomology 2)
    (hconj : ∀ σ : Gal(E/ℚ),
      realizeCoefficient E X 2
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 2) σ t) ∈
        X.pureBettiSubspace 1 1) :
    t ∈ coefficientAlgebraicClasses E X 1 := by
  let Hpq := (X.pureBettiSubspace 1 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 2)
  have ht := hScalarDescent (X.rationalCohomology 2) Hpq t hconj
  apply (Submodule.span_le.mpr ?_) ht
  rintro y ⟨a, rfl, ha⟩
  have hha : X.IsRationalHodgeClass 1 a := by
    change X.rationalCohomologyInclusion 2 a ∈ X.pureBettiSubspace 1 1
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 2
      ((1 : ℂ) ⊗ₜ[ℚ] a) ∈ X.pureBettiSubspace 1 1 at ha
    simpa only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! ha
  obtain ⟨z, hz⟩ := hDegreeTwo X a hha
  refine ⟨(1 : E) ⊗ₜ[ℚ] z, ?_⟩
  rw [LinearMap.baseChange_tmul, hz]

/-- Canonical complex conjugation of the embedding generator exchanges
the embedding with its opposite; the coefficient is exactly one. -/
theorem embeddingVector_coefficientConjugation
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E]
    (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation E (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) =
      ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) := by
  classical
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  ext σ
  rw [ComplexMultiplication.CM.TypeHodgeStructure.fieldComplexificationEquiv_conjugation,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : τ = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ
  · have h' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ = σ := by
      rw [h, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    simp [h]
  · have h' : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ ≠ σ := by
      intro he
      apply h
      rw [← he, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    simp [h, h']

end

end OAI.AlgebraicGeometry.HodgeConjecture.Coefficients.CM.SurfaceConstruction
