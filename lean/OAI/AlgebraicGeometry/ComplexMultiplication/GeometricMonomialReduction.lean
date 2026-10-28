import OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.ClassDescent

/-! # Geometric Monomial Reduction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GeometricMonomialReduction.CM.AbelianExteriorComparison

noncomputable section

/-!
# Reduction to geometric realization of balanced monomials

This is a reduction theorem, not a proof of the CM Hodge claim. Its
monomial-cycle hypothesis is a manuscript-specific obligation, explicitly
excluded from `KnownResults`. The purpose is to connect the proved
exterior support calculation and rational descent to the actual cycle map.
-/

open scoped TensorProduct Classical

variable {A : CMAbelianVariety.CM.AbelianVariety}
  {H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
  (C : KnownExteriorCohomology.CM.AbelianExteriorComparison A H)

/-- The exterior comparison with complex coefficients, followed by the
canonical map into genuine complex cohomology. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison.complexMap (n : ℕ) :
    WeightOne.CM.Complexification (⋀[ℚ]^n (A.variety.rationalCohomology 1)) →ₗ[ℂ]
      A.variety.complexCohomology n :=
  (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) n).comp
    ((C.rational n).toLinearMap.baseChange ℂ)

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison.complexMap_rational_preimage (n : ℕ) (a : A.variety.rationalCohomology n) :
    C.complexMap n ((1 : ℂ) ⊗ₜ[ℚ] (C.rational n).symm a) =
      A.variety.rationalCohomologyInclusion n a := by
  simp only [KnownExteriorCohomology.CM.AbelianExteriorComparison.complexMap, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
  rfl

local instance (D : Decomposition.CM.CMDecomposition H) : LinearOrder D.EmbeddingIndex :=
  linearOrderOfSTO WellOrderingRel

/-- Realizing all orbitwise balanced monomials suffices for an individual
genuine rational Hodge class. The monomial hypothesis still needs the
manuscript's geometric construction. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison.rational_hodge_mem_geometric_of_monomials (D : Decomposition.CM.CMDecomposition H) (p : ℕ)
    (hmonomial : ∀ s : D.ExteriorIndex (p + p),
      (∀ g, D.exteriorSignSum (p + p) s g = 0) →
      C.complexMap (p + p) (D.complexExteriorEmbeddingBasis (p + p) s) ∈
        A.variety.complexGeometricAlgebraicClasses p)
    (a : A.variety.rationalCohomology (p + p))
    (ha : a ∈ A.variety.rationalHodgeClasses p) :
    a ∈ A.variety.geometricAlgebraicClasses p := by
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) := H.finiteDimensional
  let : Module.Finite ℚ (A.variety.rationalCohomology (p + p)) :=
    Module.Finite.of_surjective (C.rational (p + p)).toLinearMap
      (C.rational (p + p)).surjective
  have hle : D.orbitBalancedExteriorSubspace (p + p) ≤
      (A.variety.complexGeometricAlgebraicClasses p).comap (C.complexMap (p + p)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨s, hs, rfl⟩
    exact hmonomial s hs
  have hx := hle (D.rational_exterior_hodge_mem_orbitBalanced p
    ((C.rational (p + p)).symm a) (C.rational_hodge_preimage p a ha))
  apply (A.variety.rational_mem_complexGeometricAlgebraicClasses_iff p a).mp
  change C.complexMap (p + p) ((1 : ℂ) ⊗ₜ[ℚ] (C.rational (p + p)).symm a) ∈
    A.variety.complexGeometricAlgebraicClasses p at hx
  rwa [C.complexMap_rational_preimage] at hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GeometricMonomialReduction.CM.AbelianExteriorComparison
