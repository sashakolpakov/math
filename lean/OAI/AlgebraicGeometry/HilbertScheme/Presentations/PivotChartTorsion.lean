import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Pivot Chart Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotChartTorsion.ProjectiveCech

noncomputable section

/-! Adding a variable to a projective chart kills kernel and cokernel elements by powers of that variable. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion.GradedModules

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem modulePivotChart_power_preimage (j : σ) (s : Finset σ) (hj : j ∉ s)
    (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M (insert j s)) :
    ∃ (k : ℕ) (y : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s),
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) y = X (R := R) j ^ k • x := by
  have h := Presentations.Module.RestrictionTorsion.GradedModules.awayModuleRestriction_power_preimage M (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (insert j s)) (LaurentMonomials.ProjectiveCech.inversionMonomial R (insert j s \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.subset_insert j s)).symm x
  change ∃ k y, Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) y =
    LaurentMonomials.ProjectiveCech.inversionMonomial R (insert j s \ s) ^ k • x at h
  simpa only [Finset.insert_sdiff_cancel hj, EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton] using h

theorem modulePivotChart_kernel_power (j : σ) (s : Finset σ) (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s)
    (hx : Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) x = 0) :
    ∃ k : ℕ, X (R := R) j ^ k • x = 0 := by
  have h := Presentations.Module.RestrictionTorsion.GradedModules.awayModuleRestriction_kernel_power M (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (LaurentMonomials.ProjectiveCech.inversionMonomial R (insert j s)) (LaurentMonomials.ProjectiveCech.inversionMonomial R (insert j s \ s))
    (LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.subset_insert j s)).symm x hx
  by_cases hj : j ∈ s
  · obtain ⟨k, hk⟩ := h
    have hx' : x = 0 := by
      simpa only [Finset.insert_eq_of_mem hj, Finset.sdiff_self, Cech.AugmentationDegree.ProjectiveCech.inversionMonomial_empty, one_pow, one_smul] using hk
    exact ⟨0, by rw [pow_zero, one_smul, hx']⟩
  · simpa only [Finset.insert_sdiff_cancel hj, EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotChartTorsion.ProjectiveCech
