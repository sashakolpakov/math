import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction

/-! # Variable Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.VariableCharts.ProjectiveCech

noncomputable section

/-! Charts on retained variables are unchanged when other variables act by arbitrary specified polynomials. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w}
variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (e i)) = X i)

include he in
theorem retainedVariable_rename (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (rename e p) = p := by
  let φ := IsScalarTower.toAlgHom R (MvPolynomial τ R) (MvPolynomial σ R)
  have h : φ.comp (rename e) = AlgHom.id R (MvPolynomial σ R) := by
    apply MvPolynomial.algHom_ext
    intro i
    change algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (rename e (X i)) = X i
    rw [rename_X]
    exact he i
  exact DFunLike.congr_fun h p

include he in
theorem retainedChartDenominator (s : Finset σ) :
    algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) = LaurentMonomials.ProjectiveCech.inversionMonomial R s := by
  rw [Cech.VariableEmbedding.ProjectiveCech.inversionMonomial_map]
  exact retainedVariable_rename R e he _

variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

def retainedModuleChartEquiv (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M (s.map e) ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M s :=
  LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (retainedChartDenominator R e he s)

theorem retainedModuleChartEquiv_degree (ℳ : ℤ → Submodule R M) (s : Finset σ) (d : ℤ) :
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (s.map e) d).map (retainedModuleChartEquiv R e he M s).toLinearMap =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d := by
  change (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ _ ((s.map e).card : ℤ) d).map _ = Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ _ (s.card : ℤ) d
  rw [Finset.card_map]
  exact LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_degree M ℳ _ _ _ (s.card : ℤ) d

variable [DecidableEq σ] [DecidableEq τ]

theorem retainedModuleChartEquiv_restriction {s t : Finset σ} (h : s ⊆ t)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M (s.map e)) :
    retainedModuleChartEquiv R e he M t (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.map_subset_map.mpr h) x) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (retainedModuleChartEquiv R e he M s x) := by
  apply LocalizationScalarRestriction.GradedModules.awayModuleScalarEquivOfEq_restriction M
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t.map e))
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (t.map e \ s.map e))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.map_subset_map.mpr h)).symm
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm
    (retainedChartDenominator R e he s) (retainedChartDenominator R e he t)
  rw [← Finset.map_sdiff]
  exact retainedChartDenominator R e he (t \ s)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.VariableCharts.ProjectiveCech
