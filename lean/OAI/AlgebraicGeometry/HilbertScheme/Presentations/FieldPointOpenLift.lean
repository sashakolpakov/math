import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.FamilyLocality

/-! # Field Point Open Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldPointOpenLift

noncomputable section

/-! Every field-valued point of a scheme factors through some member of
an open cover, with equality of the actual scheme morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fieldPoint_lift_openCover {X : Scheme.{u}} (U : X.OpenCover.{u})
    {K : Type u} [Field K] (a : Spec (CommRingCat.of K) ⟶ X) :
    ∃ i, ∃ b : Spec (CommRingCat.of K) ⟶ U.X i, b ≫ U.f i = a := by
  obtain ⟨i, y, hy⟩ := U.exists_eq (a (IsLocalRing.closedPoint K))
  have hrange : Set.range a ⊆ Set.range (U.f i) := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz]
    exact ⟨y, hy⟩
  exact ⟨i, IsOpenImmersion.lift (U.f i) a hrange, IsOpenImmersion.lift_fac _ _ _⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldPointOpenLift
