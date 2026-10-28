import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConjugationEq
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin

/-! # Analytic Realization Eq -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticRealizationEq.Constructions.AnalyticRealization

noncomputable section

/-!
# RiemannProjectivity: the complete analytic CM H¹ comparison

The rational comparison is trace evaluation on genuine lattice loops. Its
canonical extension of coefficients identifies each prescribed Hodge summand
with actual closed forms of the corresponding bidegree. The named Riemann
projectivity input also supplies a closed projective holomorphic embedding.
-/

open _root_.CategoryTheory
open scoped _root_.NumberField TensorProduct

open OAI.Geometry.ComplexTorus.RiemannProjectivity.ComparisonField.Constructions.HodgeComparison

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)

/-- The canonical complexification of the constructed rational trace comparison. -/
def complexComparison : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of Φ.periodTorus) 1 :=
  (AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of Φ.periodTorus) 1).comp
    ((ComparisonField.Constructions.FieldComparison.fieldBettiEquiv Φ).toLinearMap.baseChange ℂ)

theorem complexComparison_eq (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    complexComparison Φ x = BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x) := by
  exact ((BettiDe.Constructions.Betti.invariantBettiH1Equiv Φ).apply_symm_apply (complexComparison Φ x)).symm

theorem formClass_comparison_iff
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a) =
        complexComparison Φ x ↔
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a =
        FormsEq.Constructions.Forms.invariantH1 Φ (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x) := by
  rw [complexComparison_eq]
  exact (BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1).injective.eq_iff

/-- The positive CM signs agree exactly with the actual holomorphic Betti classes. -/
theorem holomorphic_comparison (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 0 a.val ∧
      BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a) =
        complexComparison Φ x) ↔ x ∈ Φ.hodgeStructure.holomorphic := by
  simp only [formClass_comparison_iff]
  exact (PurePrimitiveEq.Constructions.PurePrimitive.invariantH1_holomorphic_iff Φ (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x)).trans
    (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv_complexLinear_iff Φ x)

/-- The negative CM signs agree exactly with the actual antiholomorphic Betti classes. -/
theorem antiholomorphic_comparison (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 0 1 a.val ∧
      BettiDe.Constructions.Betti.deRhamBettiEquiv Φ 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodTorus 1 a) =
        complexComparison Φ x) ↔ x ∈ Φ.hodgeStructure.antiholomorphic := by
  simp only [formClass_comparison_iff]
  exact (ConjugationEq.Constructions.Conjugation.invariantH1_antiholomorphic_iff Φ (ComparisonField.Constructions.HodgeComparison.fieldComplexCovectorEquiv Φ x)).trans
    (ConjugationEq.Constructions.Conjugation.fieldComplexCovector_antilinear_iff Φ x)

/-- The same period torus carrying the checked H¹ comparison is projective
under precisely the named Riemann-projectivity input. -/
theorem projective_comparison_torus (hRiemannProjectivity : Fin.Constructions.RiemannProjectivityInput) :
    Fin.Constructions.IsProjectiveComplexTorus (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) Φ.periodIntegerLattice.toAddSubgroup :=
  Fin.Constructions.projective_period_torus hRiemannProjectivity Φ

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticRealizationEq.Constructions.AnalyticRealization
