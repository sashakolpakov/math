import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCoordinates

/-! # Coordinate Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration

noncomputable section

section

/-! Compose exact finite parameter enumeration with linear coordinates
before specializing either construction to a chosen evaluation DVR. -/

def coordinateSubspaceEnumeration {F V W I : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] (r : ℕ)
    (e : I ≃ {J : Submodule F V // Module.finrank F J = r}) (c : V ≃ₗ[F] W) :
    I ≃ {J : Submodule F W // Module.finrank F J = r} :=
  e.trans (SubspaceCoordinates.dimensionSubspaceEquiv c r)

end

/-! The coordinate enumeration retains membership of each original
subspace; changing the linear coordinate system only changes its image. -/

variable {F V W I : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  (r : ℕ) (e : I ≃ {J : Submodule F V // Module.finrank F J = r}) (c : V ≃ₗ[F] W)

theorem coordinateSubspaceEnumeration_membership (i : I) (x : V) :
    c x ∈ (coordinateSubspaceEnumeration r e c i).val ↔ x ∈ (e i).val := by
  simpa only [coordinateSubspaceEnumeration, Equiv.trans_apply, LinearEquiv.symm_apply_apply] using
    SubspaceCoordinates.dimensionSubspaceEquiv_membership c r (e i) (c x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CoordinateEnumeration
