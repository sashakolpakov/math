import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.TermMaps
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Complex Maps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexMaps.ProjectiveCech

noncomputable section

/-! Graded polynomial module maps induce morphisms of the actual Čech cochain complexes. -/

open _root_.MvPolynomial DirectSum _root_.CategoryTheory

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
  [IsScalarTower R (MvPolynomial σ R) N]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) 𝒩]

def moduleCechComplexMap (f : M →ₗ[MvPolynomial σ R] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) :
    CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d ⟶ CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R N 𝒩 d :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (TermMaps.ProjectiveCech.moduleCechTermMap R ℳ 𝒩 f hf d q)) (by
    intro q
    rw [CechComplex.ProjectiveCech.moduleCechComplex_d, CechComplex.ProjectiveCech.moduleCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (TermMaps.ProjectiveCech.moduleCechTermMap_differential R ℳ 𝒩 f hf d q x).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexMaps.ProjectiveCech
