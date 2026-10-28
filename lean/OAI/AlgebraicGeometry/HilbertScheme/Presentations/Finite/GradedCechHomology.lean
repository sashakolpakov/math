import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.FreeCechHomology
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.ComplexSequences
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.ModuleCechHomology
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules

/-! # Graded Cech Homology -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech

noncomputable section

/-! Every positive augmented Čech cohomology module of a finite graded polynomial module over a noetherian ring is finite, in every internal degree. -/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem finiteGradedCech_homology_finite_above (r : ℕ) :
    ∀ (D : GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) (d : ℤ) (q : ℕ), Fintype.card σ < q + 1 + r →
      Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R D.Carrier D.grading d).homology (q + 1)) := by
  induction r with
  | zero =>
    intro D d q hq
    exact Bounded.ModuleCechHomology.ProjectiveCech.moduleCech_homology_finite_of_bounded R D.Carrier D.grading d (q + 1) (by simpa only [Nat.add_zero] using hq)
  | succ r ih =>
    intro D d q hq
    let : Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R D.syzygy.Carrier D.syzygy.grading d).homology (q + 1 + 1)) :=
      ih D.syzygy d (q + 1) (by omega)
    let : Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R D.freeModule.Carrier D.freeModule.grading d).homology (q + 1)) :=
      FreeCechHomology.ProjectiveCech.freeModuleCech_homology_finite R D.cover.generators D.cover.degree d q
    exact ModuleCech.ComplexSequences.ProjectiveCech.moduleCech_homology_finite_of_exact R D.syzygy.grading D.freeModule.grading D.grading
      D.kernelInclusion D.projection D.kernelInclusion_homogeneous D.projection_homogeneous D.cover_exact
      D.kernelInclusion_injective D.projection_surjective d (q + 1)

theorem finiteGradedCech_homology_finite (D : GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) (d : ℤ) (q : ℕ) :
    Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R D.Carrier D.grading d).homology (q + 1)) :=
  finiteGradedCech_homology_finite_above R (Fintype.card σ + 1) D d q (by omega)

theorem moduleCech_homology_finite (M : Type (max u v)) [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [Module.Finite (MvPolynomial σ R) M] (d : ℤ) (q : ℕ) :
    Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology (q + 1)) :=
  finiteGradedCech_homology_finite R (GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule.ofModule M ℳ) d q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech
