import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Polynomial Scalars -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech

noncomputable section

/-! The actual Čech differential commutes with the whole polynomial-ring action. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleChartRestriction_polynomial_smul {s t : Finset σ} (h : s ⊆ t)
    (a : MvPolynomial σ R) (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (a • x) = a • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h x :=
  (Presentations.Module.ModuleRestriction.GradedModules.awayModuleRestriction M _ _ _ (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R h).symm).map_smul a x

theorem moduleCechDifferential_polynomial_smul (a : MvPolynomial σ R)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (a • f) = a • ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f := by
  funext s
  change (∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M
    (Finset.erase_subset i s) (a • f (s.erase i))) =
    a • ∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M
      (Finset.erase_subset i s) (f (s.erase i))
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [moduleChartRestriction_polynomial_smul, smul_comm]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars.ProjectiveCech
