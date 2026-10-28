import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.RestrictionHomExt

/-! # Equiv Compatibility -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivCompatibility.Geometry

noncomputable section

/-! Restricting the same affine equivalence preserves the original
commuting square on section rings, as well as the common reduced open. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X₁ X₂ : Over (Spec (CommRingCat.of R)))
  (U₁ : X₁.left.Opens) (U₂ : X₂.left.Opens)
  (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
  (e : EquivGeometry.ring R X₁ U₁ ≃ₐ[R] EquivGeometry.ring R X₂ U₂)
  {Y : Scheme.{u}} (f₁ : Y ⟶ X₁.left) (f₂ : Y ⟶ X₂.left)
  (h : f₁ ⁻¹ᵁ U₁ = f₂ ⁻¹ᵁ U₂)
  (he : CommRingCat.ofHom e.toRingHom ≫ f₂.appLE U₂ (f₁ ⁻¹ᵁ U₁) h.le = f₁.app U₁)
  (V : X₁.left.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U₁)

include hV in
theorem section_compatibility :
    CommRingCat.ofHom (EquivGeometry.sectionEquiv R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU).toRingHom ≫
      f₂.appLE (EquivGeometry.targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V) (f₁ ⁻¹ᵁ V)
        (EquivReduction.Geometry.target_preimage R X₁ X₂ U₁ U₂ hU₁ hU₂ e f₁ f₂ h he V hVU).le =
    f₁.app V := by
  apply Affine.RestrictionHomExt.hom_ext U₁ V hU₁ hV hVU
  have heV : X₁.left.presheaf.map (homOfLE hVU).op ≫
      CommRingCat.ofHom (EquivGeometry.sectionEquiv R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU).toRingHom =
    CommRingCat.ofHom e.toRingHom ≫ X₂.left.presheaf.map
      (homOfLE (EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)).op := by
    ext a
    exact EquivRestriction.Geometry.sectionEquiv_restriction R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU a
  rw [← Category.assoc, heV, Category.assoc, Scheme.Hom.map_appLE]
  have hr := f₂.appLE_map (U := U₂) h.le (homOfLE (f₁.preimage_mono hVU)).op
  rw [← hr, ← Category.assoc, he]
  exact (f₁.naturality (homOfLE hVU).op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivCompatibility.Geometry
