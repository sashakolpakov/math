import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology

/-! # Background -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Background.CM.Abelian

/-!
Interface bridges for CMAbelianVariety. Additional graph inputs identified here are
DegreeTwo (weight-one and degree-two algebraicity) and ExteriorCohomology (exterior cohomology).
Their full committed propositions are explicit named hypotheses; no statement
stub is imported or applied. DegreeTwo's degree-two clause already has the geometric
cycle normalization required by CMReduction, unlike the first-Chern formulation ChernClass.
-/

open _root_.CategoryTheory

/-- The weight-one clause of the committed DegreeTwo specification. -/
def WeightOneAlgebraicityInput : Prop :=
  ∀ (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1),
    (∀ x ∈ A.h1Holomorphic, u.baseChange ℂ x ∈ B.h1Holomorphic) →
    (∀ x ∈ A.h1Antiholomorphic, u.baseChange ℂ x ∈ B.h1Antiholomorphic) →
    ∃ n : ℕ, 0 < n ∧
      ∃ g : B.toOver ⟶ A.toOver,
        IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u

/-- DegreeTwo's positive denominator gives the rational scalar used by CMReduction. -/
theorem rationalH1MapsAreAlgebraic_of_DegreeTwo
    (hDegreeTwo_weight_one : WeightOneAlgebraicityInput) :
    ComplexMultiplication.KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic := by
  intro A B u hu10 hu01
  obtain ⟨n, hn, g, hg, heq⟩ := hDegreeTwo_weight_one A B u hu10 hu01
  refine ⟨(n : ℚ)⁻¹, g, hg, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [heq, smul_smul, inv_mul_cancel₀ hnq, one_smul]

/-- The degree-two clause of the committed DegreeTwo specification. -/
def DegreeTwoAlgebraicityInput : Prop :=
  ∀ (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : V.rationalCohomology 2),
    V.IsRationalHodgeClass 1 a →
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.geometricCycleClassMap 1 z = a

/-- DegreeTwo's cycle witness is precisely membership in the geometric image. -/
theorem lefschetzOneOne_of_DegreeTwo
    (hDegreeTwo_degree_two : DegreeTwoAlgebraicityInput) :
    ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne := by
  intro V a ha
  exact hDegreeTwo_degree_two V a ha

/-- Exact ExteriorCohomology specification, including the normalization on cup products. -/
def ExteriorCohomologyInput : Prop :=
  ∀ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)),
    H.holomorphic = A.h1Holomorphic →
    H.antiholomorphic = A.h1Antiholomorphic →
    Nonempty (ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H)

/-- ExteriorCohomology has exactly CMReduction's exterior-cohomology interface. -/
theorem abelianExteriorCohomology_of_ExteriorCohomology
    (hExteriorCohomology : ExteriorCohomologyInput) :
    ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology :=
  hExteriorCohomology

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Background.CM.Abelian
