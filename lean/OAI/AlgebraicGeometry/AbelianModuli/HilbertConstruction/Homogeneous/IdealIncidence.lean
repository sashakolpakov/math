import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationMatrices
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! # Ideal Incidence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IdealIncidence

noncomputable section

/-!
The degree relations of an actual homogeneous ideal satisfy the constructed
multiplication incidence matrices. Linear coordinate changes preserve the
underlying submodule-containment condition exactly.
-/

universe u v w v' w'

section LinearCoordinates

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {V' : Type v'} [AddCommGroup V'] [Module R V']
variable {W' : Type w'} [AddCommGroup W'] [Module R W']

theorem coordinate_submodule_incidence_iff (e : V ≃ₗ[R] V') (h : W ≃ₗ[R] W')
    (L : V →ₗ[R] W) (F : V' →ₗ[R] W') (hc : ∀ x, F (e x) = h (L x))
    (N : Submodule R V) (P : Submodule R W) :
    N.map e.toLinearMap ≤ (P.map h.toLinearMap).comap F ↔ N ≤ P.comap L := by
  constructor
  · intro hi x hx
    have him := hi (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
    change F (e x) ∈ P.map h.toLinearMap at him
    rw [hc] at him
    obtain ⟨y, hy, he⟩ := him
    have hey : y = L x := h.injective he
    change L x ∈ P
    exact hey ▸ hy
  · intro hi y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨L x, hi hx, (hc x).symm⟩

end LinearCoordinates

variable {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (d : ℕ)

def homogeneousDegreeRelations : Submodule R (MvPolynomial.homogeneousSubmodule σ R d) :=
  (I.toIdeal.restrictScalars R).comap (MvPolynomial.homogeneousSubmodule σ R d).subtype

def homogeneousCoordinateRelations : Submodule R (Coordinates.HomogeneousMonomials σ d → R) :=
  (homogeneousDegreeRelations I d).map (Coordinates.homogeneousCoordinates R σ d).toLinearMap

omit [Finite σ] in
theorem homogeneousDegreeRelations_multiply (i : σ) :
    homogeneousDegreeRelations I d ≤
      (homogeneousDegreeRelations I (d + 1)).comap (MultiplicationMatrices.homogeneousMultiplyX R σ d i) := by
  intro p hp
  exact I.toIdeal.mul_mem_left (MvPolynomial.X i) hp

theorem homogeneousCoordinateRelations_incidence (i : σ) :
    homogeneousCoordinateRelations I d ≤
      (homogeneousCoordinateRelations I (d + 1)).comap
        (Matrix.toLin' (MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i)) := by
  apply (coordinate_submodule_incidence_iff (Coordinates.homogeneousCoordinates R σ d)
    (Coordinates.homogeneousCoordinates R σ (d + 1)) (MultiplicationMatrices.homogeneousMultiplyX R σ d i)
    (Matrix.toLin' (MultiplicationMatrices.homogeneousMultiplicationMatrix R σ d i))
    (MultiplicationMatrices.homogeneousMultiplicationMatrix_represents R σ d i)
    (homogeneousDegreeRelations I d) (homogeneousDegreeRelations I (d + 1))).mpr
  exact homogeneousDegreeRelations_multiply I d i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IdealIncidence
