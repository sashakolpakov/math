import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PureCovectorsOf

/-! # Periods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Periods.Constructions.HodgePeriods

noncomputable section

/-!
# DegreeTwo: the genuine Hodge pieces in period coordinates

The invariant-form characterization of the canonical Hodge pieces, combined
with actual exponential-loop integration, identifies the holomorphic Betti
piece by its covectors on the actual period lattice.
-/

open _root_.CategoryTheory _root_.Manifold
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianPeriodsTo.Constructions.AbelianPeriods

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- At its own basepoint the preferred chart has identity tangent derivative. -/
theorem preferredTangentEquiv_apply (x : M) (v : E) :
    Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x v = v := by
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) x v = v
  rw [mfderiv_extChartAt_self]
  rfl

theorem preferredTangentEquiv_symm_apply (x : M) (v : E) :
    (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).symm v = v := by
  apply (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := E) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, preferredTangentEquiv_apply]

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.IsIntegral A.toOver.left :=
  A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : AlgebraicGeometry.Smooth A.toOver.hom :=
  A.variety.presentation.smooth

/-- The model-covector comparison uses the same invariant form as our period
calculation; the preferred tangent-chart map is proved to be the identity. -/
theorem modelCovectorBetti_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) :
    AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1 α =
      (A.variety.deRhamBettiIso 1).hom
        (A.variety.deRhamClass 1 (AbelianPeriodsTo.Constructions.AbelianPeriods.invariantClosedForm A α)) := by
  let a : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1 :=
    ⟨AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm α, AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm_mem α⟩
  have ha : (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel)
      (G := A.variety.analyticSpace) 1).symm α = a := by
    apply (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).injective
    erw [LinearEquiv.apply_symm_apply]
    ext w
    change α w = AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm α 1
      (fun i => (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := A.variety.analyticModel)
        (1 : A.variety.analyticSpace)).symm (w i))
    erw [AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantRawForm_one]
    apply congrArg α
    funext i
    exact (preferredTangentEquiv_symm_apply (1 : A.variety.analyticSpace) (w i)).symm
  change (A.variety.deRhamBettiIso 1).hom
    (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantDeRham 1 ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).symm α)) = _
  erw [ha]
  rfl

/-- The covector-to-Betti comparison has exactly the calculated lattice values. -/
theorem modelCovectorBetti_periods (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (α : Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ) (ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1 α) ℓ =
      α (fun _ => (ℓ : Transport.Constructions.AbelianModel A)) := by
  rw [modelCovectorBetti_eq]
  exact AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods_invariantForm hHolomorphicAlgebraicity A α ℓ

/-- An actual Betti class is holomorphic exactly when its lattice periods
are the restrictions of a pure (1,0) covector. -/
theorem holomorphic_iff_pure_periods (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : A.variety.complexCohomology 1) :
    x ∈ A.variety.pureBettiSubspace 1 0 ↔
      ∃ α : Transport.Constructions.AbelianModel A [⋀^Fin 1]→L[ℝ] ℂ,
        Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (Transport.Constructions.AbelianModel A) 1 0 α ∧
          ∀ ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A x ℓ = α (fun _ => (ℓ : Transport.Constructions.AbelianModel A)) := by
  constructor
  · intro hx
    let α := (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1).symm x
    refine ⟨α, ?_, ?_⟩
    · exact (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 α).mp
        (by simpa [α] using hx)
    · intro ℓ
      simpa [α] using modelCovectorBetti_periods hHolomorphicAlgebraicity A α ℓ
  · rintro ⟨α, hα, hperiods⟩
    have he : x = AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1 α := by
      apply (AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A).injective
      ext ℓ
      exact (hperiods ℓ).trans (modelCovectorBetti_periods hHolomorphicAlgebraicity A α ℓ).symm
    rw [he]
    exact (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 α).mpr hα

/-- The actual holomorphic Betti piece consists precisely of lattice
restrictions of complex-linear covectors, as required by the BettiLattice model. -/
theorem holomorphic_iff_complexLinear_periods (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : A.variety.complexCohomology 1) :
    x ∈ A.variety.pureBettiSubspace 1 0 ↔
      ∃ f : Transport.Constructions.AbelianModel A →ₗ[ℂ] ℂ,
        ∀ ℓ : AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, AbelianPeriodsTo.Constructions.AbelianPeriods.complexPeriods hHolomorphicAlgebraicity A x ℓ = f (ℓ : Transport.Constructions.AbelianModel A) := by
  rw [holomorphic_iff_pure_periods hHolomorphicAlgebraicity A x]
  constructor
  · rintro ⟨α, hα, hp⟩
    exact ⟨(PureCovectorsOf.Constructions.PureCovectors.complexLinearOfPure α hα).toLinearMap, hp⟩
  · rintro ⟨f, hf⟩
    refine ⟨Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector (Transport.Constructions.AbelianModel A) f.toContinuousLinearMap,
      Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree _ _, ?_⟩
    exact hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Periods.Constructions.HodgePeriods
