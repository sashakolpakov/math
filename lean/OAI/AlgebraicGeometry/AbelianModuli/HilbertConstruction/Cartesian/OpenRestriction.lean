import Mathlib.AlgebraicGeometry.Restrict

/-! # Open Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenRestriction

noncomputable section

/-! Restricting a Cartesian square to an open subset of its base gives an actual Cartesian square with explicitly specified maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g) (U : S.Opens)

include H

theorem cartesian_preimage_eq : a ⁻¹ᵁ (f ⁻¹ᵁ U) = b ⁻¹ᵁ (g ⁻¹ᵁ U) :=
  congrArg (fun k : P ⟶ S => k ⁻¹ᵁ U) H.w

def restrictedCartesianFirst : (b ⁻¹ᵁ (g ⁻¹ᵁ U)).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  a.resLE (f ⁻¹ᵁ U) (b ⁻¹ᵁ (g ⁻¹ᵁ U)) (cartesian_preimage_eq H U).symm.le

theorem restrictedCartesianFirst_comp_ι :
    restrictedCartesianFirst H U ≫ (f ⁻¹ᵁ U).ι = (b ⁻¹ᵁ (g ⁻¹ᵁ U)).ι ≫ a :=
  a.resLE_comp_ι _

theorem restrictedCartesianSquare :
    IsPullback (restrictedCartesianFirst H U) (b ∣_ (g ⁻¹ᵁ U)) (f ∣_ U) (g ∣_ U) := by
  have h : b ⁻¹ᵁ (g ⁻¹ᵁ U) = a ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ b ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [cartesian_preimage_eq H U]
    exact (inf_idem _).symm
  simpa only [restrictedCartesianFirst, Scheme.Hom.resLE_eq_morphismRestrict] using
    Scheme.Hom.isPullback_resLE H le_rfl le_rfl h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenRestriction
