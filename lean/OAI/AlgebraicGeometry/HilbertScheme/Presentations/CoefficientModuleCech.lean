import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Boundaries

/-! # Coefficient Module Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCech.ProjectiveCech

noncomputable section

/-! Compatible enlargement of coefficient scalars identifies actual Čech cochains and boundaries. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type u}
variable (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable (M : Type t) [AddCommGroup M] [Module R M] [Module S M]
  [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ S) M]
  [IsScalarTower R S M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ S) M] [IsScalarTower S (MvPolynomial σ S) M]
  [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) M]

def coefficientModuleCechEquiv : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M ≃ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) S M :=
  LinearEquiv.piCongrRight (fun s => CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s)

omit [IsScalarTower R S M] [Module S M] [IsScalarTower S (MvPolynomial σ S) M] in
theorem coefficientModuleCechEquiv_apply (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (s : Finset σ) :
    coefficientModuleCechEquiv R S M f s = CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s (f s) := rfl

omit [IsScalarTower R S M] [Module S M] [IsScalarTower S (MvPolynomial σ S) M] in
theorem coefficientModuleCechEquiv_card (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported S M q (coefficientModuleCechEquiv R S M f) ↔ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f := by
  constructor
  · intro h s hs
    apply (CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s).injective
    rw [map_zero]
    exact h s hs
  · intro h s hs
    rw [coefficientModuleCechEquiv_apply, h s hs, map_zero]

variable [LinearOrder σ]

omit [IsScalarTower R S M] in
theorem coefficientModuleCechEquiv_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    coefficientModuleCechEquiv R S M (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) =
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential S M (coefficientModuleCechEquiv R S M f) := by
  funext s
  change CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M s
    (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s) (f (s.erase i))) =
    ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign S s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction S M (Finset.erase_subset i s)
      (CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S M (s.erase i) (f (s.erase i)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv_restriction, ← algebraMap_smul S, CoefficientModuleCharts.ProjectiveCech.alternatingSign_algebraMap]

omit [IsScalarTower R S M] in
theorem coefficient_moduleCech_boundary_iff (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R M q ↔
      coefficientModuleCechEquiv R S M f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule S M q := by
  rw [Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule, Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule]
  constructor
  · rintro ⟨g, hgc, hgd⟩
    refine ⟨coefficientModuleCechEquiv R S M g, (coefficientModuleCechEquiv_card R S M (q - 1) g).mpr hgc, ?_⟩
    rw [← coefficientModuleCechEquiv_differential, hgd]
  · rintro ⟨g, hgc, hgd⟩
    obtain ⟨h, rfl⟩ := (coefficientModuleCechEquiv R S M).surjective g
    refine ⟨h, (coefficientModuleCechEquiv_card R S M (q - 1) h).mp hgc, ?_⟩
    apply (coefficientModuleCechEquiv R S M).injective
    rw [coefficientModuleCechEquiv_differential, hgd]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCech.ProjectiveCech
