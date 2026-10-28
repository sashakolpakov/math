import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedCechHomology
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseExactness

/-! # Cech Kernel Quotients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CechKernelQuotients.ProjectiveCech

noncomputable section

/-! Finiteness of Čech cohomology in the concrete kernel-quotient form used by fiberwise exactness. -/

open _root_.MvPolynomial DirectSum _root_.CategoryTheory

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleCech_kernelQuotient_finite (d : ℤ) (q : ℕ) :
    Module.Finite R (FiberwiseExactness.linearKernelCohomology R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d q)
        (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1))
        (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d q)) := by
  let K := ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d
  let f := ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d q
  let g := ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1)
  let S : ShortComplex (ModuleCat R) := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d q x)
  let : Module.Finite R (K.homology (q + 1)) := GradedCechHomology.ProjectiveCech.moduleCech_homology_finite R M ℳ d q
  let e := K.homologyIsoSc' q (q + 1) (q + 1 + 1)
    ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)
  have hfinite : Module.Finite R ((K.sc' q (q + 1) (q + 1 + 1)).homology) :=
    Module.Finite.of_surjective e.hom.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have heq : K.sc' q (q + 1) (q + 1 + 1) = S := by
    dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', K]
    simp only [ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d]
    rfl
  let : Module.Finite R S.homology := heq ▸ hfinite
  exact Module.Finite.of_surjective S.moduleCatHomologyIso.hom.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CechKernelQuotients.ProjectiveCech
