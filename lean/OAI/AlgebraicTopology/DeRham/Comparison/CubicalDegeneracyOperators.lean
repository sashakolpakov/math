import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import Mathlib.Data.Fin.Tuple.Basic

/-! # Cubical Degeneracy Operators -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracyOperators

/-!
# Genuine degeneracy operators on smooth Euclidean cubes

A cubical degeneracy is precomposition by the linear map deleting one
coordinate. The equivalent coordinate-independence condition below is an
explicit statement about the underlying smooth map, not extra geometric data.
-/

open OAI.AlgebraicTopology.DeRham.Comparison.StokesF.SingularCubeStokes
open scoped ContDiff

variable {n m : ℕ}

/-- The continuous linear map deleting the coordinate `i`. -/
def forgetCoordinate (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (i.succAbove j)

@[simp]
theorem forgetCoordinate_apply (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ)
    (j : Fin n) : forgetCoordinate i x j = x (i.succAbove j) := rfl

theorem forgetCoordinate_eq_removeNth (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    forgetCoordinate i x = Fin.removeNth i x := rfl

@[simp]
theorem forgetCoordinate_update (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (t : ℝ) :
    forgetCoordinate i (Function.update x i t) = forgetCoordinate i x := by
  ext j
  simp [Fin.succAbove_ne]

@[simp]
theorem forgetCoordinate_basis_self (i : Fin (n + 1)) :
    forgetCoordinate i (Pi.single i 1) = 0 := by
  ext j
  simp [Fin.succAbove_ne]

@[simp]
theorem forgetCoordinate_basis_succAbove (i : Fin (n + 1)) (j : Fin n) :
    forgetCoordinate i (Pi.single (i.succAbove j) 1) = Pi.single j 1 := by
  ext k
  simp [Pi.single_apply]

/-- Precomposition by coordinate deletion is the standard cubical degeneracy. -/
def cubeDegeneracy (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (i : Fin (n + 1)) :
    StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m where
  toFun := σ.toFun ∘ forgetCoordinate i
  smooth := σ.smooth.comp (forgetCoordinate i).contDiff

@[simp]
theorem cubeDegeneracy_apply (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) :
    cubeDegeneracy σ i x = σ (forgetCoordinate i x) := rfl

/-- A smooth cube ignores coordinate `i` if changing just that coordinate
never changes the value of its underlying function. -/
def IgnoresCoordinate (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (i : Fin n) : Prop :=
  ∀ (x : Fin n → ℝ) (t : ℝ), σ (Function.update x i t) = σ x

/-- An actual coordinate-degenerate smooth cube. -/
def IsDegenerateCube (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m) : Prop :=
  ∃ i : Fin n, IgnoresCoordinate σ i

theorem cubeDegeneracy_ignoresCoordinate (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1)) : IgnoresCoordinate (cubeDegeneracy σ i) i := by
  intro x t
  simp

theorem isDegenerate_cubeDegeneracy (σ : StokesF.SingularCubeStokes.SmoothSingularCube n m)
    (i : Fin (n + 1)) : IsDegenerateCube (cubeDegeneracy σ i) :=
  ⟨i, cubeDegeneracy_ignoresCoordinate σ i⟩

/-- Coordinate independence is exactly the image of a standard degeneracy.
The lower-dimensional smooth cube is obtained by fixing that coordinate to zero. -/
theorem isDegenerateCube_iff (σ : StokesF.SingularCubeStokes.SmoothSingularCube (n + 1) m) :
    IsDegenerateCube σ ↔
      ∃ (τ : StokesF.SingularCubeStokes.SmoothSingularCube n m) (i : Fin (n + 1)), cubeDegeneracy τ i = σ := by
  constructor
  · rintro ⟨i, hi⟩
    let τ : StokesF.SingularCubeStokes.SmoothSingularCube n m :=
      { toFun := fun x => σ (Fin.insertNth i 0 x)
        smooth := σ.smooth.comp (by
          apply contDiff_pi.mpr
          intro j
          by_cases hji : j = i
          · subst j
            simpa only [Fin.insertNth_apply_same] using
              (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin n → ℝ => (0 : ℝ)))
          · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
            simpa only [Fin.insertNth_apply_succAbove] using
              (contDiff_apply (𝕜 := ℝ) (E := ℝ) k :
                ContDiff ℝ ∞ (fun x : Fin n → ℝ => x k))) }
    refine ⟨τ, i, ?_⟩
    ext1
    funext x
    change σ (Fin.insertNth i 0 (forgetCoordinate i x)) = σ x
    rw [forgetCoordinate_eq_removeNth, Fin.insertNth_removeNth]
    exact hi x 0
  · rintro ⟨τ, i, rfl⟩
    exact isDegenerate_cubeDegeneracy τ i

theorem not_isDegenerate_zero_cube (σ : StokesF.SingularCubeStokes.SmoothSingularCube 0 m) :
    ¬ IsDegenerateCube σ := by
  rintro ⟨i, _⟩
  exact Fin.elim0 i

end OAI.AlgebraicTopology.DeRham.Comparison.CubicalDegeneracyOperators
