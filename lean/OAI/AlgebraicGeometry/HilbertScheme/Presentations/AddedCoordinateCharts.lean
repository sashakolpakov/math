import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateFinsets
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.VariableCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizedDegrees
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Added Coordinate Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateCharts.ProjectiveCech

noncomputable section

/-! The extra faces in an enlarged coordinate cover are actual charts of the module localized at the added linear form. -/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedLocalizedDegrees.GradedModules

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)

include he hl in
theorem addedChartDenominator (s : Finset σ) :
    algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) =
      l * LaurentMonomials.ProjectiveCech.inversionMonomial R s := by
  rw [EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ⊥ (Finset.mem_insert_self _ _),
    AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_erase_bot, map_mul, hl]
  congr 1
  exact VariableCharts.ProjectiveCech.retainedChartDenominator R Function.Embedding.coeWithBot he s

variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]

def addedModuleChartEquiv (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Presentations.Module.Fractions.GradedModules.AwayModule l M) s :=
  (LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
    (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) (addedChartDenominator R he l hl s)).trans
    ((IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M l (LaurentMonomials.ProjectiveCech.inversionMonomial R s)).restrictScalars R).symm

variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
variable (hlhom : l ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R 1)

def addedModuleChartDegreeEquiv (s : Finset σ) (d : ℤ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) d ≃ₗ[R]
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) s d := by
  have hc : ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).card : ℤ) = 1 + (s.card : ℤ) := by
    rw [AddedCoordinateFinsets.ProjectiveCech.card_addedCoordinateFace, Nat.cast_add, Nat.cast_one, add_comm]
  let E₁ := LinearEquiv.ofEq (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) d)
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) (1 + (s.card : ℤ)) d)
    (by simp only [Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree, hc])
  let E₂ := LocalizationDenominatorImage.GradedModules.awayModuleScalarDegreeEquivOfEq (R := R) M ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (addedChartDenominator R he l hl s) (1 + (s.card : ℤ)) d
  let E₃ := IteratedLocalizedDegrees.GradedModules.iteratedLocalizedDegreeEquiv (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ l (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    1 (s.card : ℤ) hlhom (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d
  exact E₁.trans (E₂.trans E₃.symm)

include hlhom in
theorem addedModuleChartEquiv_degree (s : Finset σ) (d : ℤ) :
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) d).map (addedModuleChartEquiv R he l hl M s).toLinearMap =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) s d := by
  let F := LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
    (l * LaurentMonomials.ProjectiveCech.inversionMonomial R s) (addedChartDenominator R he l hl s)
  let E := (IteratedModuleLocalization.GradedModules.iteratedAwayModuleEquiv M l (LaurentMonomials.ProjectiveCech.inversionMonomial R s)).restrictScalars R
  have hc : ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).card : ℤ) = 1 + (s.card : ℤ) := by
    rw [AddedCoordinateFinsets.ProjectiveCech.card_addedCoordinateFace, Nat.cast_add, Nat.cast_one, add_comm]
  change (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).card : ℤ) d).map
    (E.symm.toLinearMap.comp F.toLinearMap) = _
  rw [Submodule.map_comp, hc, LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_degree]
  rw [← IteratedLocalizedDegrees.GradedModules.iteratedAwayModuleEquiv_degree (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ l (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    1 (s.card : ℤ) hlhom (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d]
  rw [← Submodule.map_comp]
  have heq : E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact E.symm_apply_apply x
  rw [heq, Submodule.map_id]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateCharts.ProjectiveCech
