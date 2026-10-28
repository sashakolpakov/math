import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum

/-! # Vanishing Reference Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.VanishingReferenceTheta.CM

noncomputable section

/-! Vanishing on the original ball detects the class on the actual
reference cover, with its own marked lattice. The original period and
finite input are used throughout. -/

open scoped Classical _root_.Manifold TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice)

theorem representative_zero
    (hzero : ∀ z ∈ B.domain, ∀ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ = 0)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω) : ω = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Theta.Matching.CM.forms_eq_of_cover_evaluations E
    (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2) X N π hπ
  intro z ξ
  exact (hω z ξ).trans (hzero z.val z.property ξ)

theorem class_zero
    (hzero : ∀ z ∈ B.domain, ∀ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ = 0)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [FiniteDimensional ℚ (X.rationalCohomology 1)]
    (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θ =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 ω.val)) : θ = 0 := by
  apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace X.toOver) 1
  rw [hθ, representative_zero E L φ P hΛ hzero X N π hπ ω hω]
  simp only [ZeroMemClass.coe_zero, map_zero]

theorem nonzero_class_detected
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [FiniteDimensional ℚ (X.rationalCohomology 1)]
    (N : ℕ) (π : B.Domain → X.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover N X π)
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hω : GeometricSource.CM.RepresentsTheta E L φ X π ω)
    (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θ =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 ω.val)) (hne : θ ≠ 0) :
    ∃ z ∈ B.domain, ∃ ξ, GeometricSource.CM.thetaOneForm E L φ z ξ ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (class_zero E L φ P hΛ h X N π hπ ω hω θ hθ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.VanishingReferenceTheta.CM
