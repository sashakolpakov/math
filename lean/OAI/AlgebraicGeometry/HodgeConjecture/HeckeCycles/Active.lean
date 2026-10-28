import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors

/-! # Active -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Active.CM.Hecke

noncomputable section

/-! The rational Hecke action is Hodge compatible because clearing an
integer denominator gives an actual algebraic pullback, as in TateComparison.
Commutation comes from its commutative Hecke algebra. All algebraic
projectors are then constructed by the checked spectral argument. -/

open scoped Classical TensorProduct
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseLift.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projectors.CM

theorem rational_operator_isHodgeMap
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hH : AlbaneseLift.CM.CanonicalHolomorphic Y H)
    (T : Module.End ℚ (Y.rationalCohomology 1))
    (h_TateComparison : ∃ (n : ℕ), 0 < n ∧ ∃ f : Y.toOver ⟶ Y.toOver,
      (n : ℚ) • T = AlbaneseLift.CM.bettiPullback f) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap H H T := by
  obtain ⟨n, hn, f, hf⟩ := h_TateComparison
  apply (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H H T).mp
  apply (((ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H).restrictScalars ℚ).smul_mem_iff
    (Nat.cast_ne_zero.mpr hn.ne' : (n : ℚ) ≠ 0)).mp
  rw [← LinearMap.baseChange_smul, hf]
  exact (ComplexMultiplication.Hodge.MapDescent.CM.baseChange_mem_hodgeHomSubspace_iff H H (AlbaneseLift.CM.bettiPullback f)).mpr
    (GeometricSource.CM.actual_restriction_isHodgeMap f H H hH hH)

theorem rational_hecke_commutes
    {V A : Type*} [AddCommGroup V] [Module ℚ V] [CommRing A] [Algebra ℚ A]
    (T : A →ₐ[ℚ] Module.End ℚ V) (a b : A) : Commute (T a) (T b) := by
  change T a * T b = T b * T a
  rw [← map_mul, ← map_mul, mul_comm]

/-- Construct the projectors from a geometric rational Hecke action.
The input concerning operators is precisely an actual denominator clearing;
Hodge compatibility, spectral decomposition and all conjugate ranges follow. -/
theorem geometric_active_projectors
    (E : IntermediateField ℚ ℂ) [NumberField E]
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hH : AlbaneseLift.CM.CanonicalHolomorphic Y H)
    {A Φ : Type*} [CommRing A] [Algebra ℚ A]
    (T : A →ₐ[ℚ] Module.End ℚ (Y.rationalCohomology 1))
    (h_TateComparison : ∀ a, ∃ (n : ℕ), 0 < n ∧ ∃ f : Y.toOver ⟶ Y.toOver,
      (n : ℚ) • T a = AlbaneseLift.CM.bettiPullback f)
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1)) :
    ∃ K : IntermediateField ℚ ℂ, NumberField K ∧ IsGalois ℚ K ∧ E ≤ K ∧
      ∃ (n : ℕ) (p : Fin n → K ⊗[ℚ]
        (Y.rationalCohomology 1 →ₗ[ℚ] Y.rationalCohomology 1)),
        let P := fun i => ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K _ _ (p i)
        let S := fun i => LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K _ _ (p i))
        (∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace K (S i) 1) ∧
        (∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H) ∧
        (∀ i, ∃ φ, P i (theta φ) ≠ 0) ∧
        (∀ φ, ∑ i, P i (theta φ) = theta φ) ∧
        (∀ i, ∃ χ : A → ℂ, LinearMap.range (P i) =
          HeckeCharacters.CM.Projectors.jointSpace (fun a => (T a).baseChange ℂ) χ) ∧
        (∀ i (σ : Gal(K/ℚ)),
          let Pσ := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K _ _
            (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K _ σ (p i))
          Pσ ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H ∧
            ∃ χ : A → ℂ, LinearMap.range Pσ =
              HeckeCharacters.CM.Projectors.jointSpace (fun a => (T a).baseChange ℂ) χ) :=
  Projectors.CM.construct_algebraic_active_projectors E H T
    (rational_hecke_commutes T) (fun a => rational_operator_isHodgeMap Y H hH (T a) (h_TateComparison a))
    theta

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Active.CM.Hecke
