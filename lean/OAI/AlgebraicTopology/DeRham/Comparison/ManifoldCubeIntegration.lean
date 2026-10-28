import OAI.AlgebraicTopology.DeRham.Comparison.NormedManifoldPullback
import OAI.AlgebraicTopology.DeRham.Comparison.ComplexStokes
import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.AlgebraicTopology.DeRham.Comparison.NormalizedIntegrationNaturality
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback
import OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegenerateIntegration

/-! # Manifold Cube Integration -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration

noncomputable section

section

/-!
# Actual integration of smooth manifold forms over smooth cubes

A cube is a globally smooth map from a Euclidean parameter space into the
manifold. Its integral is the genuine pullback integral over the standard unit
cube. Stokes follows from the proved manifold pullback derivative law and the
proved Euclidean Stokes theorem; no comparison isomorphism is assumed.
-/

open Set _root_.MeasureTheory OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped _root_.Manifold ContDiff

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- An actual globally smooth cube with values in a smooth manifold. -/
@[ext]
structure SmoothManifoldCube (n : ℕ) where
  toFun : (Fin n → ℝ) → M
  smooth : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, E) ∞ toFun

variable {E M} {n k : ℕ}

instance : CoeFun (SmoothManifoldCube E M n) (fun _ => (Fin n → ℝ) → M) :=
  ⟨SmoothManifoldCube.toFun⟩

/-- Face restriction is composition with the genuine coordinate face inclusion. -/
def manifoldCubeFace (sigma : SmoothManifoldCube E M (n + 1))
    (i : Fin (n + 1)) (epsilon : ℝ) : SmoothManifoldCube E M n where
  toFun := sigma.toFun ∘ StokesF.SingularCubeStokes.faceInclusion i epsilon
  smooth := by
    have hface : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞
        (StokesF.Stokes.coordinateFace i epsilon) :=
      (StokesF.Stokes.smooth_coordinateFace i epsilon).contMDiff
    exact ContMDiff.comp sigma.smooth hface

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Pull a manifold form back to the actual Euclidean parameter space. -/
def manifoldCubePullback (sigma : SmoothManifoldCube E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm (Fin n → ℝ) k :=
  (Analysis.DifferentialForms.Manifold.NormedSpace.smoothFormManifoldEquiv (E := Fin n → ℝ) (n := k)).symm.toLinearMap.comp
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth)

@[simp]
theorem manifoldCubePullback_apply (sigma : SmoothManifoldCube E M n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    manifoldCubePullback sigma form =
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth form).toNormedSpace := rfl

/-- This is the established manifold pullback law transported through the
proved agreement of manifold and normed-space forms. -/
theorem manifoldCubePullback_d (sigma : SmoothManifoldCube E M n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    manifoldCubePullback sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (manifoldCubePullback sigma form) := by
  change (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form)).toNormedSpace =
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth form).toNormedSpace
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toNormedSpace_d]

/-- Restricting a cube to a face is ordinary derivative pullback on the
Euclidean parameter space. -/
theorem manifoldCubePullback_face (sigma : SmoothManifoldCube E M (n + 1))
    (i : Fin (n + 1)) (epsilon : ℝ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    manifoldCubePullback (manifoldCubeFace sigma i epsilon) form =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (StokesF.SingularCubeStokes.faceInclusion i epsilon) (StokesF.Stokes.smooth_coordinateFace i epsilon)
        (manifoldCubePullback sigma form) := by
  have hcompose := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp
    (E := Fin n → ℝ) (F := Fin (n + 1) → ℝ) (G := E)
    (StokesF.Stokes.coordinateFace i epsilon) (StokesF.Stokes.smooth_coordinateFace i epsilon).contMDiff
    sigma.toFun sigma.smooth form
  calc
    _ = (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (StokesF.Stokes.coordinateFace i epsilon)
        (StokesF.Stokes.smooth_coordinateFace i epsilon).contMDiff
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth form)).toNormedSpace := by
      exact congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.toNormedSpace hcompose
    _ = _ := NormedManifoldPullback.toNormedSpace_pullback_self (StokesF.Stokes.coordinateFace i epsilon)
      (StokesF.Stokes.smooth_coordinateFace i epsilon)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth form)

/-- Integration is complex-linear in the actual manifold differential form. -/
def manifoldCubeIntegration (sigma : SmoothManifoldCube E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n →ₗ[ℂ] ℂ :=
  (ComplexCubeIntegration.smoothComplexIntegration (StokesF.SingularCubeStokes.idCube n)).comp (manifoldCubePullback sigma)

@[simp]
theorem manifoldCubeIntegration_apply (sigma : SmoothManifoldCube E M n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldCubeIntegration sigma form =
      ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.idCube n) (manifoldCubePullback sigma form) := rfl

/-- The definition is precisely the Bochner integral of the pullback form
on the standard oriented frame of the unit parameter cube. -/
theorem manifoldCubeIntegration_eq_integral (sigma : SmoothManifoldCube E M n)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldCubeIntegration sigma form =
      ∫ x in Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1),
        manifoldCubePullback sigma form x (fun j => Pi.single j 1) := by
  rw [manifoldCubeIntegration_apply,
    ComplexCubeIntegration.complexIntegrateForm_eq_integral _ _ (manifoldCubePullback sigma form).smooth]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  simp [ComplexCubeIntegration.complexCubeIntegrand, StokesF.Stokes.identityCube]

/-- Face integration agrees with Euclidean face integration of the pulled-back form. -/
theorem manifoldCubeIntegration_face (sigma : SmoothManifoldCube E M (n + 1))
    (i : Fin (n + 1)) (epsilon : ℝ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldCubeIntegration (manifoldCubeFace sigma i epsilon) form =
      ComplexCubeIntegration.complexIntegrateForm (StokesF.SingularCubeStokes.singularFace (StokesF.SingularCubeStokes.idCube (n + 1)) i epsilon)
        (manifoldCubePullback sigma form) := by
  rw [manifoldCubeIntegration_apply, manifoldCubePullback_face]
  rw [ComplexCubeIntegration.complexIntegrateForm_eq_integral _ _
      (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback (StokesF.SingularCubeStokes.faceInclusion i epsilon) (StokesF.Stokes.smooth_coordinateFace i epsilon)
        (manifoldCubePullback sigma form)).smooth,
    ComplexCubeIntegration.complexIntegrateForm_eq_integral _ _ (manifoldCubePullback sigma form).smooth]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  exact (NormalizedIntegrationNaturality.complexCubeIntegrand_postcompose (StokesF.Stokes.coordinateFace i epsilon)
    (StokesF.Stokes.smooth_coordinateFace i epsilon) (StokesF.SingularCubeStokes.idCube n)
    (manifoldCubePullback sigma form) x).symm

/-- Stokes' theorem on an actual smooth cube in a smooth manifold. -/
theorem manifoldCubeStokes (sigma : SmoothManifoldCube E M (n + 1))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    manifoldCubeIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form) =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) •
        (manifoldCubeIntegration (manifoldCubeFace sigma i 1) form -
          manifoldCubeIntegration (manifoldCubeFace sigma i 0) form) := by
  rw [manifoldCubeIntegration_apply, manifoldCubePullback_d]
  simp only [manifoldCubeIntegration_face, Analysis.DifferentialForms.Manifold.Basic.SmoothForm.coe_d]
  exact ComplexStokes.complexSingularStokes (StokesF.SingularCubeStokes.idCube (n + 1)) (manifoldCubePullback sigma form)
    (manifoldCubePullback sigma form).smooth

end

/-!
# Naturality and actual degeneracies of manifold-cube integration

Precomposition and postcomposition use actual smooth maps. A coordinate-
degenerate cube is one whose value is unchanged when that coordinate changes.
Such cubes are proved to have zero integral, providing the geometric input for
normalized manifold-cube chains.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped _root_.Manifold ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  {n d k : ℕ}

/-- Change a cube's parameterization by an actual smooth Euclidean map. -/
def manifoldCubePrecompose (g : (Fin d → ℝ) → (Fin n → ℝ)) (hg : ContDiff ℝ ∞ g)
    (sigma : SmoothManifoldCube E M n) : SmoothManifoldCube E M d where
  toFun := sigma.toFun ∘ g
  smooth := sigma.smooth.comp hg.contMDiff

/-- Push a cube forward by an actual smooth map of manifolds. -/
def manifoldCubePostcompose (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (sigma : SmoothManifoldCube E M n) : SmoothManifoldCube F N n where
  toFun := f ∘ sigma.toFun
  smooth := hf.comp sigma.smooth

/-- The standard coordinate degeneracy of a manifold-valued smooth cube. -/
def manifoldCubeDegeneracy (sigma : SmoothManifoldCube E M n) (i : Fin (n + 1)) :
    SmoothManifoldCube E M (n + 1) :=
  manifoldCubePrecompose (CubicalDegeneracyOperators.forgetCoordinate i) (CubicalDegeneracyOperators.forgetCoordinate i).contDiff sigma

/-- Coordinate independence is an actual equality of the underlying maps. -/
def ManifoldCubeIgnoresCoordinate (sigma : SmoothManifoldCube E M n) (i : Fin n) : Prop :=
  ∀ (x : Fin n → ℝ) (t : ℝ), sigma (Function.update x i t) = sigma x

/-- A geometrically coordinate-degenerate manifold-valued cube. -/
def IsDegenerateManifoldCube (sigma : SmoothManifoldCube E M n) : Prop :=
  ∃ i : Fin n, ManifoldCubeIgnoresCoordinate sigma i

theorem manifoldCubeDegeneracy_ignoresCoordinate (sigma : SmoothManifoldCube E M n)
    (i : Fin (n + 1)) : ManifoldCubeIgnoresCoordinate (manifoldCubeDegeneracy sigma i) i := by
  intro x t
  change sigma (CubicalDegeneracyOperators.forgetCoordinate i (Function.update x i t)) = sigma (CubicalDegeneracyOperators.forgetCoordinate i x)
  rw [CubicalDegeneracyOperators.forgetCoordinate_update]

/-- Every coordinate-independent cube factors through the genuine coordinate deletion. -/
theorem isDegenerateManifoldCube_iff (sigma : SmoothManifoldCube E M (n + 1)) :
    IsDegenerateManifoldCube sigma ↔
      ∃ (tau : SmoothManifoldCube E M n) (i : Fin (n + 1)),
        manifoldCubeDegeneracy tau i = sigma := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨i, hcoordinate⟩ := h
    let tau : SmoothManifoldCube E M n :=
      { toFun := fun y => sigma (Fin.insertNth (α := fun _ => ℝ) i 0 y)
        smooth := sigma.smooth.comp (StokesF.Stokes.smooth_coordinateFace i 0).contMDiff }
    refine ⟨tau, i, ?_⟩
    apply SmoothManifoldCube.ext
    funext x
    have hreset : Fin.insertNth (α := fun _ => ℝ) i 0 (CubicalDegeneracyOperators.forgetCoordinate i x) = Function.update x i 0 := by
      funext a
      induction a using Fin.succAboveCases i with
      | x => simp
      | p j => simp [CubicalDegeneracyOperators.forgetCoordinate_apply, Fin.succAbove_ne]
    change sigma (Fin.insertNth (α := fun _ => ℝ) i 0 (CubicalDegeneracyOperators.forgetCoordinate i x)) = sigma x
    exact (congrArg sigma hreset).trans (hcoordinate x 0)
  · rintro ⟨tau, i, heq⟩
    refine ⟨i, ?_⟩
    intro x t
    rw [← heq]
    change tau (CubicalDegeneracyOperators.forgetCoordinate i (Function.update x i t)) = tau (CubicalDegeneracyOperators.forgetCoordinate i x)
    exact congrArg tau (CubicalDegeneracyOperators.forgetCoordinate_update i x t)

variable [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- Parameter pullback agrees with ordinary differential-form pullback. -/
theorem manifoldCubePullback_precompose
    (g : (Fin d → ℝ) → (Fin n → ℝ)) (hg : ContDiff ℝ ∞ g)
    (sigma : SmoothManifoldCube E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M k) :
    manifoldCubePullback (manifoldCubePrecompose g hg sigma) form =
      Analysis.DifferentialForms.Manifold.Basic.SmoothForm.pullback g hg (manifoldCubePullback sigma form) := by
  change (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (sigma.toFun ∘ g)
      (sigma.smooth.comp hg.contMDiff) form).toNormedSpace = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp (E := Fin d → ℝ) (F := Fin n → ℝ)
    (G := E) g hg.contMDiff sigma.toFun sigma.smooth form]
  exact NormedManifoldPullback.toNormedSpace_pullback_self g hg
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback sigma.toFun sigma.smooth form)

/-- Pulling a form along a pushed-forward cube is ordinary manifold functoriality. -/
theorem manifoldCubePullback_postcompose (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (sigma : SmoothManifoldCube E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N k) :
    manifoldCubePullback (manifoldCubePostcompose f hf sigma) form =
      manifoldCubePullback sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form) := by
  change (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (f ∘ sigma.toFun)
      (hf.comp sigma.smooth) form).toNormedSpace = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp (E := Fin n → ℝ) (F := E) (G := F)
    sigma.toFun sigma.smooth f hf form]
  rfl

/-- Parameterized manifold integration agrees with Euclidean integration of
its actual pulled-back form on the same parameterized cube. -/
theorem manifoldCubeIntegration_precompose
    (g : (Fin d → ℝ) → (Fin n → ℝ)) (hg : ContDiff ℝ ∞ g)
    (sigma : SmoothManifoldCube E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M d) :
    manifoldCubeIntegration (manifoldCubePrecompose g hg sigma) form =
      ComplexCubeIntegration.complexIntegrateForm (CubicalDegenerateQ.cubePostcompose g hg (StokesF.SingularCubeStokes.idCube d))
        (manifoldCubePullback sigma form) := by
  rw [manifoldCubeIntegration_apply, manifoldCubePullback_precompose]
  exact (NormalizedIntegrationNaturality.complexIntegrateForm_postcompose g hg (StokesF.SingularCubeStokes.idCube d)
    (manifoldCubePullback sigma form)).symm

/-- Integration is natural for genuine smooth maps of manifolds. -/
theorem manifoldCubeIntegration_postcompose (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (sigma : SmoothManifoldCube E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F N n) :
    manifoldCubeIntegration (manifoldCubePostcompose f hf sigma) form =
      manifoldCubeIntegration sigma (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf form) := by
  simp only [manifoldCubeIntegration_apply, manifoldCubePullback_postcompose]

/-- The true alternating pullback integral vanishes on a standard degeneracy. -/
@[simp]
theorem manifoldCubeIntegration_degeneracy (sigma : SmoothManifoldCube E M n)
    (i : Fin (n + 1)) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n + 1)) :
    manifoldCubeIntegration (manifoldCubeDegeneracy sigma i) form = 0 := by
  change manifoldCubeIntegration
    (manifoldCubePrecompose (CubicalDegeneracyOperators.forgetCoordinate i) (CubicalDegeneracyOperators.forgetCoordinate i).contDiff sigma) form = 0
  rw [manifoldCubeIntegration_precompose]
  have hc : CubicalDegenerateQ.cubePostcompose (CubicalDegeneracyOperators.forgetCoordinate i) (CubicalDegeneracyOperators.forgetCoordinate i).contDiff
      (StokesF.SingularCubeStokes.idCube (n + 1)) = CubicalDegeneracyOperators.cubeDegeneracy (StokesF.SingularCubeStokes.idCube n) i := rfl
  rw [hc]
  exact CubicalDegenerateIntegration.complexIntegrateForm_cubeDegeneracy (StokesF.SingularCubeStokes.idCube n) i (manifoldCubePullback sigma form)

/-- Integration vanishes on every cube that is actually independent of a coordinate. -/
theorem manifoldCubeIntegration_eq_zero_of_isDegenerate
    (sigma : SmoothManifoldCube E M n) (hsigma : IsDegenerateManifoldCube sigma)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) : manifoldCubeIntegration sigma form = 0 := by
  cases n with
  | zero =>
    obtain ⟨i, _⟩ := hsigma
    exact Fin.elim0 i
  | succ n =>
    obtain ⟨tau, i, rfl⟩ := (isDegenerateManifoldCube_iff sigma).mp hsigma
    exact manifoldCubeIntegration_degeneracy tau i form

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration
