import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flat Preimmersion Reduced -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatPreimmersionReduced

noncomputable section

/-! A flat preimmersion preserves reducedness. On stalks the map is
both surjective and faithfully flat, hence an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem flat_preimmersion_isReduced {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsPreimmersion f] [Flat f] [IsReduced Y] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let φ := (f.stalkMap x).hom
    let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := φ.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom φ)
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hi : Function.Injective φ := FaithfulSMul.algebraMap_injective
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    let e := RingEquiv.ofBijective φ ⟨hi, f.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk X

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatPreimmersionReduced
