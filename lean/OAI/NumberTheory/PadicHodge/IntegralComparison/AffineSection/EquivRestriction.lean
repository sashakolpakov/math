import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivGeometry

/-! # Equiv Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivRestriction.Geometry

noncomputable section

/-! The equivalence on a smaller affine neighborhood is the restriction
of the specified original equivalence, on every actual function. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem spec_appLE {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (W : (Spec B).Opens) (hW : W ≤ (Spec.map φ) ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso A).inv ≫ (Spec.map φ).appLE ⊤ W hW =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.map (homOfLE le_top).op := by
  rw [Scheme.Hom.appLE, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

variable (R : Type u) [CommRing R]
  (X₁ X₂ : Over (Spec (CommRingCat.of R)))
  (U₁ : X₁.left.Opens) (U₂ : X₂.left.Opens)
  (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
  (e : EquivGeometry.ring R X₁ U₁ ≃ₐ[R] EquivGeometry.ring R X₂ U₂)

private theorem left_appLE (W : (EquivGeometry.common R X₁ U₁).left.Opens)
    (hW : W ≤ (EquivGeometry.left R X₁ U₁ hU₁) ⁻¹ᵁ U₁) :
    (EquivGeometry.left R X₁ U₁ hU₁).appLE U₁ W hW =
      (Scheme.ΓSpecIso Γ(X₁.left,U₁)).inv ≫
        (EquivGeometry.common R X₁ U₁).left.presheaf.map (homOfLE le_top).op := by
  change hU₁.fromSpec.appLE U₁ W hW = _
  rw [Scheme.Hom.appLE, hU₁.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rfl

private theorem right_appLE (W : (EquivGeometry.common R X₁ U₁).left.Opens)
    (hW : W ≤ (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) ⁻¹ᵁ U₂) :
    (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e).appLE U₂ W hW =
      CommRingCat.ofHom e.symm.toRingHom ≫ (Scheme.ΓSpecIso Γ(X₁.left,U₁)).inv ≫
        (EquivGeometry.common R X₁ U₁).left.presheaf.map (homOfLE le_top).op := by
  change (Spec.map (show Γ(X₂.left,U₂) ⟶ Γ(X₁.left,U₁) from
    CommRingCat.ofHom e.symm.toRingHom) ≫ hU₂.fromSpec).appLE U₂ W hW = _
  rw [Scheme.Hom.comp_appLE, hU₂.fromSpec_app_self, Category.assoc, Scheme.Hom.map_appLE]
  exact spec_appLE _ W _

private theorem right_full : (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) ⁻¹ᵁ U₂ = ⊤ :=
  (congrArg (fun O => (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) ⁻¹ᵁ O)
    (EquivGeometry.right_range R X₁ X₂ U₁ U₂ hU₂ e)).symm.trans
      (Scheme.Hom.preimage_opensRange (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e))

variable (V : X₁.left.Opens) (hVU : V ≤ U₁)

theorem sectionEquiv_apply (a : EquivGeometry.ring R X₁ V) :
    ((EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e).appIso (EquivGeometry.sourceOpen R X₁ U₁ hU₁ V)).hom
      (EquivGeometry.sectionEquiv R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU a) =
    (EquivGeometry.left R X₁ U₁ hU₁).app V a := by
  let L := EquivGeometry.left R X₁ U₁ hU₁
  let W := EquivGeometry.sourceOpen R X₁ U₁ hU₁ V
  have hl := L.app_invApp' V ((EquivGeometry.left_range R X₁ U₁ hU₁).symm ▸ hVU)
  change L.app V ≫ (L.appIso W).inv = X₁.left.presheaf.map
    (eqToHom (EquivGeometry.source_image R X₁ U₁ hU₁ V hVU)).op at hl
  have hl' := congrArg (fun k => k ≫ (L.appIso W).hom) hl
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hl'
  change ((EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e).appIso W).hom
    (((EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e).appIso W).inv
      ((L.appIso W).hom (X₁.left.presheaf.map
        (eqToHom (EquivGeometry.source_image R X₁ U₁ hU₁ V hVU)).op a))) = _
  rw [Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom hl' a).symm

theorem sectionEquiv_restriction (a : EquivGeometry.ring R X₁ U₁) :
    EquivGeometry.sectionEquiv R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hVU
      (X₁.left.presheaf.map (homOfLE hVU).op a) =
    X₂.left.presheaf.map (homOfLE (EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)).op (e a) := by
  let L := EquivGeometry.left R X₁ U₁ hU₁
  let G := EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e
  let W := EquivGeometry.sourceOpen R X₁ U₁ hU₁ V
  apply (ConcreteCategory.bijective_of_isIso (G.appIso W).hom).injective
  rw [sectionEquiv_apply]
  have hL : W ≤ L ⁻¹ᵁ U₁ := L.preimage_mono hVU
  have hG : W ≤ G ⁻¹ᵁ U₂ := by rw [right_full]; exact le_top
  have hl := ConcreteCategory.congr_hom (L.naturality (homOfLE hVU).op) a
  change L.app V (X₁.left.presheaf.map (homOfLE hVU).op a) = L.appLE U₁ W hL a at hl
  rw [hl]
  have hg := ConcreteCategory.congr_hom
    (G.map_appLE (U := G ''ᵁ W) (V := W) (G.preimage_image_eq W).ge
      (homOfLE (EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)).op) (e a)
  rw [← G.appIso_hom' W] at hg
  change (G.appIso W).hom
    (X₂.left.presheaf.map (homOfLE (EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V)).op (e a)) =
      G.appLE U₂ W hG (e a) at hg
  rw [hg, left_appLE, right_appLE]
  change _ = (EquivGeometry.common R X₁ U₁).left.presheaf.map (homOfLE le_top).op
    ((Scheme.ΓSpecIso Γ(X₁.left,U₁)).inv (e.symm (e a)))
  rw [AlgEquiv.symm_apply_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivRestriction.Geometry
