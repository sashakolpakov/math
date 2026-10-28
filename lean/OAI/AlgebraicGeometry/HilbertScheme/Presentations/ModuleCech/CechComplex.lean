import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Cech Complex -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech

noncomputable section

/-! The actual homogeneous Čech terms and differentials form a cochain complex of modules. -/

open _root_.MvPolynomial _root_.CategoryTheory

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleCechComplex (d : ℤ) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of R (Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q))
    (fun q => ModuleCat.ofHom (Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d q)) (by
      intro q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d q f)

theorem moduleCechComplex_d (d : ℤ) (q : ℕ) :
    (moduleCechComplex (σ := σ) R M ℳ d).d q (q + 1) =
      ModuleCat.ofHom (Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d q) := by
  simp only [moduleCechComplex, CochainComplex.of_d]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech
