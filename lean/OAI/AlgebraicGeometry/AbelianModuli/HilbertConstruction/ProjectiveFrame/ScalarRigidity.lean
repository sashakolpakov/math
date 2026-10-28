import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Group.Units.Basic

/-! # Scalar Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ScalarRigidity

noncomputable section

/-! A linear automorphism fixing the lines of a basis and one additional
vector whose coordinates are units is scalar. The argument works over an
arbitrary commutative ring, as required on projective-frame charts. -/
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} (b : Module.Basis κ R V)
variable (f : V →ₗ[R] V) (a : κ → R) (hf : ∀ k, f (b k) = a k • b k)

include hf in
theorem basis_diagonal_coordinate (k : κ) :
    (b.coord k).comp f = a k • b.coord k := by
  classical
  apply b.ext
  intro j
  change b.coord k (f (b j)) = a k • b.coord k (b j)
  rw [hf, map_smul]
  by_cases hj : j = k
  · subst j
    rfl
  · simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hj, ite_false, smul_zero]

include hf in
theorem projectiveFrame_linearMap_scalar
    (v : V) (hu : ∀ k, IsUnit (b.repr v k)) (c : R) (hv : f v = c • v) :
    f = c • LinearMap.id := by
  have ha (k : κ) : a k = c := by
    have h := LinearMap.congr_fun (basis_diagonal_coordinate b f a hf k) v
    change b.coord k (f v) = a k * b.coord k v at h
    rw [hv, map_smul] at h
    have h' : c * b.repr v k = a k * b.repr v k := h
    exact ((hu k).mul_right_cancel h').symm
  apply b.ext
  intro k
  change f (b k) = c • b k
  rw [hf, ha]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ScalarRigidity
