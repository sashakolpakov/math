import OAI.AlgebraicGeometry.Albanese.Construction.ProjectiveCoordinates
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-! # Segre Coordinates -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.SegreCoordinates

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The projective dimension for the tensor product of two homogeneous
coordinate vectors. -/
def segreDimension (m n : ℕ) : ℕ := m * n + m + n

/-- Index tensor coordinates by the ordinary projective coordinate type. -/
def segreIndexEquiv (m n : ℕ) : Fin (m + 1) × Fin (n + 1) ≃ Fin (segreDimension m n + 1) :=
  finProdFinEquiv.trans (finCongr (by dsimp [segreDimension]; ring))

/-- Pairwise products of homogeneous coordinates. -/
def segreVector {R : Type*} [Mul R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R) : Fin (segreDimension m n + 1) → R :=
  fun k => v ((segreIndexEquiv m n).symm k).1 * w ((segreIndexEquiv m n).symm k).2

@[simp]
theorem segreVector_pair {R : Type*} [Mul R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreVector v w (segreIndexEquiv m n (i, j)) = v i * w j := by
  simp [segreVector]

theorem segreVector_normalized {R : Type*} [MulOneClass R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R) (i : Fin (m + 1)) (j : Fin (n + 1))
    (hv : v i = 1) (hw : w j = 1) :
    segreVector v w (segreIndexEquiv m n (i, j)) = 1 := by simp [hv, hw]

/-- Tensor coordinates of two nonzero vectors over a domain are nonzero. -/
theorem segreVector_ne_zero {R : Type*} [CommRing R] [IsDomain R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R) (hv : v ≠ 0) (hw : w ≠ 0) :
    segreVector v w ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := Function.ne_iff.mp hw
  intro h
  have hz := congrFun h (segreIndexEquiv m n (i, j))
  exact (mul_ne_zero hi hj) (by simpa using hz)

/-- Changing either homogeneous representative only rescales the Segre vector. -/
theorem segreVector_smul {R : Type*} [CommRing R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R) (c d : R) :
    segreVector (c • v) (d • w) = (c * d) • segreVector v w := by
  funext k
  simp only [segreVector, Pi.smul_apply, smul_eq_mul]
  ring

/-- Segre coordinates satisfy all rank-one matrix equations. -/
theorem segreVector_minor {R : Type*} [CommRing R] {m n : ℕ}
    (v : Fin (m + 1) → R) (w : Fin (n + 1) → R)
    (i k : Fin (m + 1)) (j l : Fin (n + 1)) :
    segreVector v w (segreIndexEquiv m n (i, j)) *
        segreVector v w (segreIndexEquiv m n (k, l)) =
      segreVector v w (segreIndexEquiv m n (i, l)) *
        segreVector v w (segreIndexEquiv m n (k, j)) := by
  simp only [segreVector_pair]
  ring

/-- The local algebraic Segre morphism supplied by two normalized tuples. -/
def segreMapOfCoordinates {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {m n : ℕ}
    (v : Fin (m + 1) → Γ(X, ⊤)) (w : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (m + 1)) (j : Fin (n + 1)) (hv : v i = 1) (hw : w j = 1) :
    X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace (segreDimension m n) :=
  ProjectiveCoordinates.projectiveMapOfCoordinates f (segreVector v w) (segreIndexEquiv m n (i, j))
    (segreVector_normalized v w i j hv hw)

@[reassoc (attr := simp)]
theorem segreMapOfCoordinates_over {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {m n : ℕ}
    (v : Fin (m + 1) → Γ(X, ⊤)) (w : Fin (n + 1) → Γ(X, ⊤))
    (i : Fin (m + 1)) (j : Fin (n + 1)) (hv : v i = 1) (hw : w j = 1) :
    segreMapOfCoordinates f v w i j hv hw ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (segreDimension m n) = f :=
  ProjectiveCoordinates.projectiveMapOfCoordinates_over _ _ _ _

end

end OAI.AlgebraicGeometry.Albanese.Construction.SegreCoordinates
