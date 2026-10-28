import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Embedded Chart Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedChartRestriction.ProjectiveCech

noncomputable section

/-! Deleting variables commutes with restriction between actual projective module charts. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationScalarRestriction.GradedModules

universe u v w t

variable {σ : Type v} {τ : Type w} [DecidableEq σ] [DecidableEq τ]
variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) =
  (MvPolynomial.killCompl e.injective).toRingHom)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

theorem embeddedModuleChartEquiv_restriction {s t : Finset σ} (h : s ⊆ t)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M (s.map e)) :
    EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M t
      (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.map_subset_map.mpr h) x) =
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M s x) := by
  apply LocalizationScalarRestriction.GradedModules.awayModuleScalarEquivOfEq_restriction M
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t.map e))
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (t.map e \ s.map e))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.map_subset_map.mpr h)).symm
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm
    (EmbeddedModuleCharts.ProjectiveCech.embeddedChartDenominator R e he s) (EmbeddedModuleCharts.ProjectiveCech.embeddedChartDenominator R e he t)
  rw [← Finset.map_sdiff]
  exact EmbeddedModuleCharts.ProjectiveCech.embeddedChartDenominator R e he (t \ s)

omit [DecidableEq τ] in
theorem embeddedModuleCechValue [LinearOrder τ] (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M)
    (s t : Finset σ) (h : t ⊆ s) :
    EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M s
      (ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (s.map e) (t.map e) (Finset.map_subset_map.mpr h)) =
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M t (f (t.map e))) :=
  embeddedModuleChartEquiv_restriction R e he M h (f (t.map e))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedChartRestriction.ProjectiveCech
