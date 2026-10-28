import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Spec Local Rings -/

namespace OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings

noncomputable section

/-! The actual global function ring of a local Noetherian spectrum has
the same local and Noetherian properties, through the canonical isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem specGlobal_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRing Γ(Spec (.of R), ⊤) := by
  have : Nontrivial Γ(Spec (.of R), ⊤) :=
    RingHom.domain_nontrivial (Scheme.ΓSpecIso (.of R)).hom.hom
  exact IsLocalRing.of_surjective' (Scheme.ΓSpecIso (.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective

theorem specGlobal_isNoetherianRing (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing Γ(Spec (.of R), ⊤) :=
  isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm

end

end OAI.RepresentationTheory.Theta.Geometric.SpecLocalRings
