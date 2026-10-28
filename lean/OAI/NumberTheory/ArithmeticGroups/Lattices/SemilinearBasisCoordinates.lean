import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-! # Semilinear Basis Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearBasisCoordinates.Construction

noncomputable section

/-! Coordinate matrices commute with semilinear specialization when the
chosen bases specialize to one another. -/

open scoped Classical

theorem semilinear_map_basis_coordinates
    {R S V W ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W] [Fintype ι]
    (σ : R →+* S) (b : Module.Basis ι R V) (c : Module.Basis ι S W)
    (f : V →ₛₗ[σ] W) (hf : ∀ i, f (b i) = c i) (x : V) (i : ι) :
    c.repr (f x) i = σ (b.repr x i) := by
  have h : f x = ∑ j, σ (b.repr x j) • c j := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smulₛₗ, hf]
  rw [h]
  simp [Finsupp.single_apply]

theorem semilinear_intertwining_matrix
    {R S V W ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W] [Fintype ι]
    (σ : R →+* S) (b : Module.Basis ι R V) (c : Module.Basis ι S W)
    (f : V →ₛₗ[σ] W) (hf : ∀ i, f (b i) = c i)
    (A : Module.End R V) (B : Module.End S W) (hAB : ∀ x, f (A x) = B (f x)) :
    (LinearMap.toMatrix b b A).map σ = LinearMap.toMatrix c c B := by
  ext i j : 1
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    ← semilinear_map_basis_coordinates σ b c f hf, hAB, hf]

theorem semilinear_intertwining_determinant
    {R S V W ι : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module S W] [Fintype ι]
    (σ : R →+* S) (b : Module.Basis ι R V) (c : Module.Basis ι S W)
    (f : V →ₛₗ[σ] W) (hf : ∀ i, f (b i) = c i)
    (A : Module.End R V) (B : Module.End S W) (hAB : ∀ x, f (A x) = B (f x)) :
    σ (LinearMap.det A) = LinearMap.det B := by
  rw [← LinearMap.det_toMatrix b, RingHom.map_det, RingHom.mapMatrix_apply,
    semilinear_intertwining_matrix σ b c f hf A B hAB, LinearMap.det_toMatrix]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemilinearBasisCoordinates.Construction
