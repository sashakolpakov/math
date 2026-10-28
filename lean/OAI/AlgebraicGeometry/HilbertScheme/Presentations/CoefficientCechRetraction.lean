import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientModuleCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Retraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CechBoundaries

/-! # Coefficient Cech Retraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientCechRetraction.ProjectiveCech

noncomputable section

/-! Graded Čech exactness descends through a polynomial-module retraction after compatible coefficient enlargement. -/

open _root_.MvPolynomial DirectSum

universe u v w t z

variable {σ : Type u} [LinearOrder σ] [Fintype σ]
variable (R : Type v) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {M : Type t} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type z} [AddCommGroup N] [Module R N] [Module S N]
  [Module (MvPolynomial σ R) N] [Module (MvPolynomial σ S) N]
  [IsScalarTower R S N] [IsScalarTower R (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ S) N] [IsScalarTower S (MvPolynomial σ S) N]
  [IsScalarTower (MvPolynomial σ R) (MvPolynomial σ S) N]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
variable (𝒩 : ℤ → Submodule S N)

omit [LinearOrder σ] [Fintype σ] [IsScalarTower R S N] in
theorem coefficientCechMap_homogeneous (i : M →ₗ[MvPolynomial σ R] N)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ 𝒩 d) (d : ℤ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous S N 𝒩 d (CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv R S N (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f)) := by
  intro s
  obtain ⟨k, m, hm, hmf⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) d (f s)).mp (hf s)
  change CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv R S N s
    (Localized.GradedExactness.GradedModules.awayModuleMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) i (f s)) ∈ Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree S N 𝒩 s d
  rw [← hmf, Localized.GradedExactness.GradedModules.awayModuleMap_fraction, CoefficientModuleCharts.ProjectiveCech.coefficientModuleChartEquiv_fraction]
  exact Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree 𝒩 _ _ d k (i m) (hi _ m hm)

variable [Decomposition ℳ]

omit [Fintype σ] [IsScalarTower R S N] in
theorem moduleCechExactAt_of_coefficient_retraction
    (i : M →ₗ[MvPolynomial σ R] N) (p : N →ₗ[MvPolynomial σ R] M)
    (hi : ∀ d m, m ∈ ℳ d → i m ∈ 𝒩 d) (hpi : ∀ m, p (i m) = m)
    (d : ℤ) (q : ℕ) (hN : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) S N 𝒩 d q) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q := by
  intro f hf hfc hfd
  let E := CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv (σ := σ) R S N
  have hFh := coefficientCechMap_homogeneous R S ℳ 𝒩 i hi d f hf
  have hFc := (CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv_card R S N q (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f)).mpr
    (ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R i q f hfc)
  have hFd : ModuleCech.Card.ProjectiveCech.moduleCechDifferential S N (E (ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f)) = 0 := by
    rw [← CoefficientModuleCech.ProjectiveCech.coefficientModuleCechEquiv_differential, ← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hfd, map_zero, map_zero]
  obtain ⟨g, _, hgc, hgd⟩ := hN _ hFh hFc hFd
  have hb : ModuleCech.Maps.ProjectiveCech.moduleCechMap R i f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R N q := by
    apply (CoefficientModuleCech.ProjectiveCech.coefficient_moduleCech_boundary_iff R S N q _).mpr
    exact (Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule S N q _).mpr ⟨g, hgc, hgd⟩
  obtain ⟨h, hhc, hhd⟩ := (Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule R N q _).mp hb
  apply Homogeneous.CechBoundaries.ProjectiveCech.homogeneous_moduleCech_boundary R M ℳ d q f hf
  apply (Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule R M q f).mpr
  refine ⟨ModuleCech.Maps.ProjectiveCech.moduleCechMap R p h, ModuleCech.Maps.ProjectiveCech.moduleCechMap_card R p (q - 1) h hhc, ?_⟩
  rw [← ModuleCech.Maps.ProjectiveCech.moduleCechMap_differential, hhd, ModuleCech.Retraction.ProjectiveCech.moduleCechMap_retraction R i p hpi]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CoefficientCechRetraction.ProjectiveCech
