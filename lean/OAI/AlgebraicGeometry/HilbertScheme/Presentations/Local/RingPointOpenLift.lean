import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyLocality

/-! # Ring Point Open Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift

noncomputable section

/-! A map from the spectrum of any local ring factors through an open
cover member containing its closed point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem localRingPoint_lift_openCover {X : Scheme.{u}} (U : X.OpenCover.{u})
    {R : Type u} [CommRing R] [IsLocalRing R] (a : Spec (.of R) ⟶ X) :
    ∃ i, ∃ b : Spec (.of R) ⟶ U.X i, b ≫ U.f i = a := by
  obtain ⟨i, y, hy⟩ := U.exists_eq (a (IsLocalRing.closedPoint R))
  have hp : a (IsLocalRing.closedPoint R) ∈ (U.f i).opensRange := ⟨y, hy⟩
  have hrange : Set.range a ⊆ Set.range (U.f i) := by
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map a.continuous).mem_open (U.f i).opensRange.isOpen hp
  exact ⟨i, IsOpenImmersion.lift (U.f i) a hrange, IsOpenImmersion.lift_fac _ _ _⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RingPointOpenLift
