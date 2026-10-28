import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RationalPeriods
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConjugation

/-! # Analytic Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AnalyticRealization.CM.Abelian.GenericAnalyticRealization

noncomputable section

/-!
# RiemannProjectivity: the complete analytic generic H¹ comparison

The rational comparison is trace evaluation on genuine lattice loops. Its
canonical extension of coefficients identifies each prescribed Hodge summand
with actual closed forms of the corresponding bidegree. The named Riemann
projectivity input also supplies a closed projective holomorphic embedding.
-/

open _root_.CategoryTheory
open scoped _root_.NumberField TensorProduct

variable {U ι : Type} [AddCommGroup U] [Module ℚ U]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)
  (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
  (hRiemannProjectivity : ProjectiveTorusData.CM.Abelian.RiemannProjectivityInput)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData.ofHodgeStructure b H P hRiemannProjectivity

/-- The canonical complexification of the constructed rational polarization comparison. -/
def complexComparison : ComplexMultiplication.WeightOne.CM.Complexification U →ₗ[ℂ]
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of (D).periodTorus) 1 :=
  (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of (D).periodTorus) 1).comp
    ((RationalPeriods.CM.Abelian.polarizedRationalBettiEquiv b H P hRiemannProjectivity).toLinearMap.baseChange ℂ)

theorem complexComparison_eq (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    complexComparison b H P hRiemannProjectivity x = AlgebraicBetti.CM.Abelian.Algebraization.Betti.invariantBettiH1Equiv D (RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv b H P hRiemannProjectivity x) := by
  exact ((AlgebraicBetti.CM.Abelian.Algebraization.Betti.invariantBettiH1Equiv D).apply_symm_apply (complexComparison b H P hRiemannProjectivity x)).symm

theorem formClass_comparison_iff
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms ((D).space) (D).periodTorus 1) (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a) =
        complexComparison b H P hRiemannProjectivity x ↔
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a =
        AlgebraicForms.CM.Abelian.Algebraization.Forms.invariantH1 D (RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv b H P hRiemannProjectivity x) := by
  rw [complexComparison_eq]
  exact (AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1).injective.eq_iff

/-- The prescribed holomorphic subspace agree exactly with the actual holomorphic Betti classes. -/
theorem holomorphic_comparison (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms ((D).space) (D).periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree ((D).space) (D).periodTorus 1 0 a.val ∧
      AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a) =
        complexComparison b H P hRiemannProjectivity x) ↔ x ∈ H.holomorphic := by
  simp only [formClass_comparison_iff]
  exact (AlgebraicPurePrimitive.CM.Abelian.Algebraization.PurePrimitive.invariantH1_holomorphic_iff D (RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv b H P hRiemannProjectivity x)).trans
    (by
      rw [RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv_eq]
      exact PeriodDuality.CM.Abelian.polarizedPeriodCovector_complexLinear_iff P x)

/-- The prescribed antiholomorphic subspace agree exactly with the actual antiholomorphic Betti classes. -/
theorem antiholomorphic_comparison (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms ((D).space) (D).periodTorus 1,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree ((D).space) (D).periodTorus 0 1 a.val ∧
      AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a) =
        complexComparison b H P hRiemannProjectivity x) ↔ x ∈ H.antiholomorphic := by
  simp only [formClass_comparison_iff]
  exact (AlgebraicConjugation.CM.Abelian.Algebraization.Conjugation.invariantH1_antiholomorphic_iff D (RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv b H P hRiemannProjectivity x)).trans
    (by
      rw [RationalPeriods.CM.Abelian.polarizedComplexCovectorEquiv_eq]
      exact PeriodDuality.CM.Abelian.polarizedPeriodCovector_antilinear_iff P x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AnalyticRealization.CM.Abelian.GenericAnalyticRealization
