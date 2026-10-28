import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Field Point Open Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldPointOpenLift

noncomputable section

/-! A field-valued point lifts to any open containing its unique image point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_field_point_open_lift {S : Scheme.{0}} (U : S.Opens)
    {k : Type} [Field k] (q : Spec (.of k) ⟶ S)
    (hq : q (IsLocalRing.closedPoint k) ∈ U) :
    ∃ v : Spec (.of k) ⟶ U.toScheme, v ≫ U.ι = q := by
  have hr : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    refine ⟨⟨q x, ?_⟩, rfl⟩
    exact hx.symm ▸ hq
  exact ⟨IsOpenImmersion.lift U.ι q hr, IsOpenImmersion.lift_fac U.ι q hr⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldPointOpenLift
