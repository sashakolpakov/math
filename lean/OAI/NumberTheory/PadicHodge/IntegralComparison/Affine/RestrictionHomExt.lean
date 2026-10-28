import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Restriction Hom Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RestrictionHomExt

noncomputable section

/-! Ring maps out of an affine subopen are determined after the
original affine restriction map, since its spectrum is an open immersion. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hVU : V ≤ U)

include hU hV in
theorem hom_ext {T : CommRingCat.{u}} (a b : Γ(X,V) ⟶ T)
    (h : X.presheaf.map (homOfLE hVU).op ≫ a = X.presheaf.map (homOfLE hVU).op ≫ b) : a=b := by
  let r := Spec.map (X.presheaf.map (homOfLE hVU).op)
  have hr : r ≫ hU.fromSpec = hV.fromSpec := hU.map_fromSpec hV (homOfLE hVU).op
  let : IsOpenImmersion (r ≫ hU.fromSpec) := hr.symm ▸ inferInstance
  let : IsOpenImmersion r := IsOpenImmersion.of_comp r hU.fromSpec
  apply Spec.map_injective
  apply (cancel_mono r).mp
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RestrictionHomExt
