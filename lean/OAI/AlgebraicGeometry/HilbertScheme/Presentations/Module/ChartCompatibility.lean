import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartFractionRestriction

/-! # Chart Compatibility -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ChartCompatibility.ProjectiveCech

noncomputable section

/-! Compatibility of module charts and their free coordinates under restriction. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

omit [Fintype σ] in
theorem moduleChartRestriction_refl (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.Subset.refl s) = LinearMap.id := by
  have he : ModuleRestriction.GradedModules.awayModuleRestriction M (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (LaurentMonomials.ProjectiveCech.inversionMonomial R (s \ s)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.Subset.refl s)).symm =
      LinearMap.id := by
    apply ModuleRestriction.GradedModules.awayModuleRestriction_unique
    rfl
  exact congrArg (fun f => f.restrictScalars R) he

omit [Fintype σ] in
theorem moduleChartRestriction_comp {s t z : Finset σ} (hst : s ⊆ t) (htz : t ⊆ z) :
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M htz).comp (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M hst) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (hst.trans htz) := by
  have he : (ModuleRestriction.GradedModules.awayModuleRestriction M (LaurentMonomials.ProjectiveCech.inversionMonomial R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R z)
      (LaurentMonomials.ProjectiveCech.inversionMonomial R (z \ t)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R htz).symm).comp
      (ModuleRestriction.GradedModules.awayModuleRestriction M (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R t)
        (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R hst).symm) =
      ModuleRestriction.GradedModules.awayModuleRestriction M (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (LaurentMonomials.ProjectiveCech.inversionMonomial R z)
        (LaurentMonomials.ProjectiveCech.inversionMonomial R (z \ s)) (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (hst.trans htz)).symm := by
    symm
    apply ModuleRestriction.GradedModules.awayModuleRestriction_unique
    rw [LinearMap.comp_assoc, ModuleRestriction.GradedModules.awayModuleRestriction_comp_mk, ModuleRestriction.GradedModules.awayModuleRestriction_comp_mk]
  exact congrArg (fun f => f.restrictScalars R) he

omit [Fintype σ] in
theorem moduleChartRestriction_fraction {s t : Finset σ} (h : s ⊆ t) (k : ℕ) (m : M) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k m) =
      Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R t) k (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k • m) := by
  rw [Fractions.GradedModules.moduleFractionMap_apply, Fractions.GradedModules.moduleFractionMap_apply]
  exact ModuleRestriction.GradedModules.awayModuleRestriction_fraction M _ _ _ (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm k m

variable (ι : Type t)

theorem freeLocalizedEquiv_restriction {s t : Finset σ} (h : s ⊆ t)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (ι →₀ MvPolynomial σ R) s) (i : ι) :
    Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι t (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (ι →₀ MvPolynomial σ R) h x) i =
      LaurentRestriction.ProjectiveCech.chartRestriction R h (Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s x i) := by
  obtain ⟨k, p, rfl⟩ := Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) x
  rw [moduleChartRestriction_fraction, Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv_fraction,
    Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv_fraction, ChartFractionRestriction.ProjectiveCech.chartRestriction_fraction]
  apply congrArg (LaurentBasis.ProjectiveCech.chartFractionLinearMap R t k)
  change LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k * p i = p i * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.ChartCompatibility.ProjectiveCech
