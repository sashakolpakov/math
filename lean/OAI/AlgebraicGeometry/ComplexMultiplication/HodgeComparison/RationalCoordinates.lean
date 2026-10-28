import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalRealOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodCoordinateDuality
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Rational Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCoordinates.CM.Construction

noncomputable section

/-! Genuine rational H¹ bases give conjugate complementary coordinate
subspaces and the real period isomorphism onto the dual holomorphic space. -/

open scoped TensorProduct

variable {ι : Type} [Fintype ι]

def rationalH1ComplexBasis (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) : Module.Basis ι ℂ (V.complexCohomology 1) := by
  let : FiniteDimensional ℚ (V.rationalCohomology 1) := b.finiteDimensional_of_finite
  exact (b.baseChange ℂ).map (CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace V.toOver) 1)

theorem rationalH1ComplexBasis_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) (i : ι) :
    rationalH1ComplexBasis V b i = V.rationalCohomologyInclusion 1 (b i) := by
  change CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 ((b.baseChange ℂ) i) = _
  rw [Module.Basis.baseChange_apply, CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
  rfl

theorem rationalH1Coordinates_conjugate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) (x : ι → ℂ) :
    BettiConjugation.CM.Construction.conjugateBettiH1 V ((rationalH1ComplexBasis V b).equivFun.symm x) =
      (rationalH1ComplexBasis V b).equivFun.symm (star x) := by
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smulₛₗ]
  have hfixed : BettiConjugation.CM.Construction.conjugateBettiH1 V (rationalH1ComplexBasis V b i) = rationalH1ComplexBasis V b i := by
    rw [rationalH1ComplexBasis_apply]
    exact PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) (b i)
  rw [hfixed]
  rfl

def rationalH1HolomorphicCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) : Submodule ℂ (ι → ℂ) :=
  (V.pureBettiSubspace 1 0).comap (rationalH1ComplexBasis V b).equivFun.symm.toLinearMap

def rationalH1AntiholomorphicCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) : Submodule ℂ (ι → ℂ) :=
  (V.pureBettiSubspace 0 1).comap (rationalH1ComplexBasis V b).equivFun.symm.toLinearMap

theorem rationalH1Coordinates_isCompl (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    IsCompl (rationalH1HolomorphicCoordinates V b) (rationalH1AntiholomorphicCoordinates V b) := by
  have hD : IsCompl (V.pureDeRhamSubspace 1 0) (V.pureDeRhamSubspace 0 1) :=
    ⟨Intersection.CM.Construction.pureDeRham_one_disjoint, codisjoint_iff.mpr (OneSpanning.CM.Construction.pureDeRham_one_sup_top V)⟩
  have hB : IsCompl (V.pureBettiSubspace 1 0) (V.pureBettiSubspace 0 1) :=
    (Submodule.orderIsoMapComap (V.deRhamBettiIso 1).toLinearEquiv).isCompl_iff.mp hD
  exact (Submodule.orderIsoMapComap (rationalH1ComplexBasis V b).equivFun.symm).symm.isCompl_iff.mp hB

theorem rationalH1Coordinates_conjugate_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) (x : ι → ℂ) :
    star x ∈ rationalH1AntiholomorphicCoordinates V b ↔ x ∈ rationalH1HolomorphicCoordinates V b := by
  change (rationalH1ComplexBasis V b).equivFun.symm (star x) ∈ V.pureBettiSubspace 0 1 ↔
    (rationalH1ComplexBasis V b).equivFun.symm x ∈ V.pureBettiSubspace 1 0
  constructor
  · intro hx
    have h := BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
    rw [rationalH1Coordinates_conjugate, star_star] at h
    exact h
  · intro hx
    have h := BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx
    rwa [rationalH1Coordinates_conjugate] at h

def rationalH1PeriodEquiv (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    (ι → ℝ) ≃ₗ[ℝ] Module.Dual ℂ (rationalH1HolomorphicCoordinates V b) :=
  PeriodCoordinateDuality.CM.Construction.realPeriodEvaluationEquiv _ _ (rationalH1Coordinates_isCompl V b)
    (rationalH1Coordinates_conjugate_mem V b)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCoordinates.CM.Construction
