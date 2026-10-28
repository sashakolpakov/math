import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Similitude Dual Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SimilitudeDualLattice

noncomputable section

/-! Dual submodules commute with preimages under a similitude. This
separates the rational multiplier calculation from integral perfection. -/

variable {R K V W : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

theorem dualSubmodule_comap_similitude
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (e : V ≃ₗ[K] W) (c : K) (he : ∀ x y, C (e x) (e y) = c * B x y)
    (L : Submodule R W) :
    (C.dualSubmodule L).comap (e.toLinearMap.restrictScalars R) =
      (c • B).dualSubmodule (L.comap (e.toLinearMap.restrictScalars R)) := by
  ext x
  constructor
  · intro hx y hy
    change c * B x y ∈ (1 : Submodule R K)
    rw [← he]
    exact hx (e y) hy
  · intro hx y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    change C (e x) (e z) ∈ (1 : Submodule R K)
    rw [he]
    exact hx z hy

theorem dualSubmodule_comap_of_self_dual
    (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (e : V ≃ₗ[K] W) (c : K) (he : ∀ x y, C (e x) (e y) = c * B x y)
    (L : Submodule R W) (hL : C.dualSubmodule L = L) :
    (c • B).dualSubmodule (L.comap (e.toLinearMap.restrictScalars R)) =
      L.comap (e.toLinearMap.restrictScalars R) := by
  rw [← dualSubmodule_comap_similitude B C e c he, hL]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SimilitudeDualLattice
