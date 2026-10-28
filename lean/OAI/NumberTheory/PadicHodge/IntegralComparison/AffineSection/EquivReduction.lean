import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivRestriction

/-! # Equiv Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivReduction.Geometry

noncomputable section

/-! A specified equivalence compatible with the original reduction
maps transports every smaller affine open to the same reduced open. -/
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

def commonLift : (f₁ ⁻¹ᵁ U₁).toScheme ⟶ (EquivGeometry.common R X₁ U₁).left :=
  (f₁ ⁻¹ᵁ U₁).toSpecΓ ≫ Spec.map (f₁.app U₁)

theorem commonLift_left : commonLift R X₁ U₁ f₁ ≫ EquivGeometry.left R X₁ U₁ hU₁ =
    (f₁ ⁻¹ᵁ U₁).ι ≫ f₁ := by
  change ((f₁ ⁻¹ᵁ U₁).toSpecΓ ≫ Spec.map (f₁.app U₁)) ≫ hU₁.fromSpec = _
  rw [Scheme.Opens.toSpecΓ_naturality, Category.assoc, IsAffineOpen.toSpecΓ_fromSpec,
    morphismRestrict_ι]

include he in
theorem commonLift_right : commonLift R X₁ U₁ f₁ ≫ EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e =
    (f₁ ⁻¹ᵁ U₁).ι ≫ f₂ := by
  have hinv : CommRingCat.ofHom e.symm.toRingHom ≫ f₁.app U₁ =
      f₂.appLE U₂ (f₁ ⁻¹ᵁ U₁) h.le := by
    rw [← he, ← Category.assoc]
    have hi : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom = 𝟙 _ := by
      ext a
      exact e.apply_symm_apply a
    rw [hi, Category.id_comp]
  change ((f₁ ⁻¹ᵁ U₁).toSpecΓ ≫ Spec.map (f₁.app U₁)) ≫
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ hU₂.fromSpec) = _
  calc
    _ = (f₁ ⁻¹ᵁ U₁).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom e.symm.toRingHom ≫ f₁.app U₁) ≫ hU₂.fromSpec := by
      rw [Spec.map_comp]
      simp only [Category.assoc]
    _ = _ := by
      rw [hinv, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
        IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

include he in
theorem target_preimage (V : X₁.left.Opens) (hVU : V ≤ U₁) :
    f₁ ⁻¹ᵁ V = f₂ ⁻¹ᵁ EquivGeometry.targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V := by
  let a := commonLift R X₁ U₁ f₁
  let L := EquivGeometry.left R X₁ U₁ hU₁
  let G := EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e
  have hl := commonLift_left R X₁ U₁ hU₁ f₁
  have hr := commonLift_right R X₁ X₂ U₁ U₂ hU₂ e f₁ f₂ h he
  apply le_antisymm
  · intro y hy
    have hyU : y ∈ f₁ ⁻¹ᵁ U₁ := hVU hy
    let v : (f₁ ⁻¹ᵁ U₁).toScheme := ⟨y,hyU⟩
    have hlv : L (a v) = f₁ y := congrArg (fun k => k v) hl
    have hrv : G (a v) = f₂ y := congrArg (fun k => k v) hr
    refine ⟨a v, ?_, hrv⟩
    change L (a v) ∈ V
    rw [hlv]
    exact hy
  · intro y hy
    have hyU₂ : y ∈ f₂ ⁻¹ᵁ U₂ := EquivGeometry.target_below R X₁ X₂ U₁ U₂ hU₁ hU₂ e V hy
    have hyU₁ : y ∈ f₁ ⁻¹ᵁ U₁ := h.ge hyU₂
    let v : (f₁ ⁻¹ᵁ U₁).toScheme := ⟨y,hyU₁⟩
    have hlv : L (a v) = f₁ y := congrArg (fun k => k v) hl
    have hrv : G (a v) = f₂ y := congrArg (fun k => k v) hr
    obtain ⟨x,hx,hxy⟩ := hy
    have hxv : x = a v := G.isOpenEmbedding.injective (hxy.trans hrv.symm)
    rw [hxv] at hx
    change L (a v) ∈ V at hx
    change f₁ y ∈ V
    rw [← hlv]
    exact hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivReduction.Geometry
