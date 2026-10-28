import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.DualFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.BoundaryCenterCoordinates

/-! # Boundary Center Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCenterCoordinates.Construction

noncomputable section

/-! Adapt a framed center to actual boundary equations presented only up to units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k]

/-- The input boundary equations need only admit an explicit étale
normal-crossing model. A principal localization recovers exact dual
derivations, and the center and every original equation are then retained
in simultaneous coordinates through the original prime. -/
theorem exists_modeled_boundary_center_coordinates
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    {n : ℕ} (w : Fin n → R) (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R (Fin n) w)
    (hw : ∀ j, w j ∈ Ideal.span (Set.range g))
    (p : PrimeSpectrum R) (hp : Ideal.span (Set.range g) ≤ p.asIdeal) :
    Nonempty (Boundary.CoordinateCenterChart.Construction.BoundaryCoordinateCenterOpenChart k R (Ideal.span (Set.range g)) w p) := by
  obtain ⟨t, ht, E, hE⟩ := M.exists_local_dual_frame p.asIdeal (fun j => hp (hw j))
  let A := Localization.Away t
  let f : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  obtain ⟨Q, hQ⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime t p ht
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    IsOpenImmersion.of_isLocalization t
  exact Open.BoundaryCenterCoordinates.Construction.exists_boundary_center_coordinates_of_open_dual_frame k R (.of A) f
    g D hD w E hE hw p hp Q hQ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.BoundaryCenterCoordinates.Construction
