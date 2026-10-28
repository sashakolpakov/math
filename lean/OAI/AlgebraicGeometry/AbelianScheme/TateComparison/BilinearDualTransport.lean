import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SimilitudeDualLattice

/-! # Bilinear Dual Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearDualTransport

noncomputable section

/-! An actual change of coordinates transports dual submodules. -/

variable {R K V W : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]

theorem bilinearDualSubmodule_congr (B : LinearMap.BilinForm K V)
    (e : V ≃ₗ[K] W) (L : Submodule R V) :
    (LinearMap.BilinForm.congr e B).dualSubmodule (L.map (e.toLinearMap.restrictScalars R)) =
      (B.dualSubmodule L).map (e.toLinearMap.restrictScalars R) := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    have hh := hx (e y) ⟨y, hy, rfl⟩
    simpa only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply] using hh
  · rintro ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
    change B (e.symm (e x)) (e.symm (e y)) ∈ (1 : Submodule R K)
    simpa only [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply] using hx y hy

theorem bilinearSelfDual_congr (B : LinearMap.BilinForm K V)
    (e : V ≃ₗ[K] W) (L : Submodule R V) (hL : B.dualSubmodule L = L) :
    (LinearMap.BilinForm.congr e B).dualSubmodule (L.map (e.toLinearMap.restrictScalars R)) =
      L.map (e.toLinearMap.restrictScalars R) := by
  rw [bilinearDualSubmodule_congr, hL]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BilinearDualTransport
