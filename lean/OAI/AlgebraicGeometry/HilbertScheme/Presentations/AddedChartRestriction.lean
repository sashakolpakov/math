import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizationRestriction

/-! # Added Chart Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedChartRestriction.ProjectiveCech

noncomputable section

/-! Added-coordinate chart identifications commute with the actual projective restrictions. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizationRestriction.GradedModules

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]

theorem addedModuleChartEquiv_restriction {s t : Finset σ} (h : s ⊆ t)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) :
    AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M t (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_subset h) x) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Presentations.Module.Fractions.GradedModules.AwayModule l M) h (AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M s x) := by
  let Eₛ := LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
    (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) (AddedCoordinateCharts.ProjectiveCech.addedChartDenominator R he l hl s)
  let Eₜ := LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace t))
    (l * LaurentMonomials.ProjectiveCech.inversionMonomial R t) (AddedCoordinateCharts.ProjectiveCech.addedChartDenominator R he l hl t)
  let Lₛ := (IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M l (LaurentMonomials.ProjectiveCech.inversionMonomial R s)).restrictScalars R
  let Lₜ := (IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M l (LaurentMonomials.ProjectiveCech.inversionMonomial R t)).restrictScalars R
  apply Lₜ.injective
  change Lₜ (Lₜ.symm (Eₜ (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_subset h) x))) =
    Lₜ (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Presentations.Module.Fractions.GradedModules.AwayModule l M) h (Lₛ.symm (Eₛ x)))
  rw [LinearEquiv.apply_symm_apply]
  have hc : l * LaurentMonomials.ProjectiveCech.inversionMonomial R t = (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) := by
    rw [mul_assoc, LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h]
  have hres := IteratedLocalizationRestriction.GradedModules.iteratedAwayModuleEquiv_restriction M l (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t)
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm (Lₛ.symm (Eₛ x))
  change Lₜ (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Presentations.Module.Fractions.GradedModules.AwayModule l M) h (Lₛ.symm (Eₛ x))) =
    Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) (l * LaurentMonomials.ProjectiveCech.inversionMonomial R t)
      (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) hc (Lₛ (Lₛ.symm (Eₛ x))) at hres
  rw [LinearEquiv.apply_symm_apply] at hres
  rw [hres]
  apply LocalizationScalarRestriction.GradedModules.awayModuleScalarEquivOfEq_restriction M
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace t))
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace t \ AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_subset h)).symm
    (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) (l * LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) hc
    (AddedCoordinateCharts.ProjectiveCech.addedChartDenominator R he l hl s) (AddedCoordinateCharts.ProjectiveCech.addedChartDenominator R he l hl t)
  rw [AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_sdiff]
  exact VariableCharts.ProjectiveCech.retainedChartDenominator R Function.Embedding.coeWithBot he (t \ s)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedChartRestriction.ProjectiveCech
