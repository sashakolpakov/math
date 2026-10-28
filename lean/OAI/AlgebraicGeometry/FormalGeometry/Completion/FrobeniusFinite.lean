import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Frobenius Finite -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFinite.Construction

noncomputable section

/-! The actual q-power scheme Frobenius is finite on finite-type schemes over the finite field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [Fintype k]

/-- Every element is integral over the image of the actual q-power ring map. -/
theorem finiteFieldPowerRingHom_isIntegral {R : Type u} [CommRing R] (κ : k →+* R) :
    (Frobenius.Construction.finiteFieldPowerRingHom k κ).IsIntegral := by
  let : Algebra R R := (Frobenius.Construction.finiteFieldPowerRingHom k κ).toAlgebra
  intro r
  apply _root_.IsIntegral.of_pow (n := Fintype.card k) Fintype.card_pos
  change _root_.IsIntegral R (algebraMap R R r)
  exact isIntegral_algebraMap

variable (X : Scheme.{u}) (κ : k →+* Γ(X, ⊤))

/-- Absolute q-power Frobenius has the same affine-open preimages. -/
instance qPowerSchemeFrobenius_affine : IsAffineHom (Frobenius.Construction.qPowerSchemeFrobenius k X κ) where
  isAffine_preimage _ hU := hU

/-- Integrality of the actual Frobenius is checked on its actual section maps. -/
instance qPowerSchemeFrobenius_integral : IsIntegralHom (Frobenius.Construction.qPowerSchemeFrobenius k X κ) where
  isIntegral_app U _ := finiteFieldPowerRingHom_isIntegral k (Frobenius.Construction.sectionBaseMap k X κ U)

variable (A : Over (Spec (CommRingCat.of k)))

/-- Finite type plus actual integrality proves finiteness of the actual relative q-power map. -/
theorem finiteFieldSchemeFrobenius_finite [LocallyOfFiniteType A.hom] :
    IsFinite (Frobenius.Construction.finiteFieldSchemeFrobenius k A).left := by
  have : IsIntegralHom (Frobenius.Construction.finiteFieldSchemeFrobenius k A).left :=
    qPowerSchemeFrobenius_integral k A.left (Frobenius.Construction.varietyBaseMap k A)
  have : LocallyOfFiniteType ((Frobenius.Construction.finiteFieldSchemeFrobenius k A).left ≫ A.hom) := by
    rw [(Frobenius.Construction.finiteFieldSchemeFrobenius k A).w]
    infer_instance
  have : LocallyOfFiniteType (Frobenius.Construction.finiteFieldSchemeFrobenius k A).left :=
    locallyOfFiniteType_of_comp _ A.hom
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- The actual q-power map is surjective because it fixes the underlying points. -/
theorem finiteFieldSchemeFrobenius_surjective : Surjective (Frobenius.Construction.finiteFieldSchemeFrobenius k A).left :=
  ⟨fun x => ⟨x, rfl⟩⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFinite.Construction
