import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Free
import Mathlib.Algebra.Exact.Basic

/-! # Graded Polynomial Modules -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules

noncomputable section

/-! Finite graded polynomial modules and their constructed free covers and syzygies. -/

open _root_.MvPolynomial DirectSum

universe u v

structure FiniteGradedPolynomialModule (σ : Type v) (R : Type u) [CommRing R] where
  Carrier : Type (max u v)
  [addCommGroup : AddCommGroup Carrier]
  [baseModule : Module R Carrier]
  [polynomialModule : Module (MvPolynomial σ R) Carrier]
  [scalarTower : IsScalarTower R (MvPolynomial σ R) Carrier]
  grading : ℤ → Submodule R Carrier
  [decomposition : Decomposition grading]
  [gradedSMul : SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) grading]
  [finiteModule : Module.Finite (MvPolynomial σ R) Carrier]

attribute [instance] FiniteGradedPolynomialModule.addCommGroup
  FiniteGradedPolynomialModule.baseModule FiniteGradedPolynomialModule.polynomialModule
  FiniteGradedPolynomialModule.scalarTower FiniteGradedPolynomialModule.decomposition
  FiniteGradedPolynomialModule.gradedSMul FiniteGradedPolynomialModule.finiteModule

namespace FiniteGradedPolynomialModule

variable {σ : Type v} {R : Type u} [CommRing R]

def ofModule (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M] (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [Module.Finite (MvPolynomial σ R) M] : FiniteGradedPolynomialModule σ R where
  Carrier := M
  grading := ℳ

variable (D : FiniteGradedPolynomialModule σ R)

def cover : Graded.Free.GradedModules.HomogeneousFreeCover (σ := σ) R D.grading := Graded.Free.GradedModules.homogeneousFreeCover R D.grading

def freeModule : FiniteGradedPolynomialModule σ R where
  Carrier := D.cover.FreeModule
  grading := WeightedFreeModules.GradedModules.weightedFreeGrading R D.cover.degree

def projection : D.freeModule.Carrier →ₗ[MvPolynomial σ R] D.Carrier :=
  Graded.Free.GradedModules.HomogeneousFreeCover.map R D.grading D.cover

theorem projection_surjective : Function.Surjective D.projection :=
  Graded.Free.GradedModules.HomogeneousFreeCover.map_surjective R D.grading D.cover

theorem projection_homogeneous (d : ℤ) (x : D.freeModule.Carrier)
    (hx : x ∈ D.freeModule.grading d) : D.projection x ∈ D.grading d :=
  Graded.Free.GradedModules.HomogeneousFreeCover.map_homogeneous R D.grading D.cover d x hx

variable [Finite σ] [IsNoetherianRing R]

def syzygy : FiniteGradedPolynomialModule σ R where
  Carrier := (Graded.Free.GradedModules.HomogeneousFreeCover.map R D.grading D.cover).ker
  grading := D.cover.kernelGrading

def kernelInclusion : D.syzygy.Carrier →ₗ[MvPolynomial σ R] D.freeModule.Carrier :=
  D.projection.ker.subtype

theorem kernelInclusion_injective : Function.Injective D.kernelInclusion := Subtype.val_injective

theorem kernelInclusion_homogeneous (d : ℤ) (x : D.syzygy.Carrier)
    (hx : x ∈ D.syzygy.grading d) : D.kernelInclusion x ∈ D.freeModule.grading d := hx

theorem cover_exact : Function.Exact D.kernelInclusion D.projection :=
  LinearMap.exact_subtype_ker_map D.projection

end FiniteGradedPolynomialModule

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules
