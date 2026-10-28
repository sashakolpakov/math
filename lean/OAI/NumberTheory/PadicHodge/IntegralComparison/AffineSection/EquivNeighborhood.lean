import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivReduction

/-! # Equiv Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivNeighborhood.Geometry

noncomputable section

/-! Control the target of a restricted original frame by choosing
its source neighborhood inside the exact inverse image. -/
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

def sourceFor (W : X₂.left.Opens) : X₁.left.Opens :=
  (EquivGeometry.left R X₁ U₁ hU₁) ''ᵁ ((EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) ⁻¹ᵁ W)

theorem sourceFor_below (W : X₂.left.Opens) : sourceFor R X₁ X₂ U₁ U₂ hU₁ hU₂ e W ≤ U₁ :=
  ((EquivGeometry.left R X₁ U₁ hU₁).image_le_opensRange _).trans (EquivGeometry.left_range R X₁ U₁ hU₁).le

theorem target_below_of_sourceFor (V : X₁.left.Opens) (W : X₂.left.Opens)
    (hVW : V ≤ sourceFor R X₁ X₂ U₁ U₂ hU₁ hU₂ e W) :
    EquivGeometry.targetOpen R X₁ X₂ U₁ U₂ hU₁ hU₂ e V ≤ W := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := hy
  obtain ⟨x',hx',he⟩ := hVW hx
  have he' : x'=x := (EquivGeometry.left R X₁ U₁ hU₁).isOpenEmbedding.injective he
  subst x'
  exact hx'

theorem sourceFor_contains {Y : Scheme.{u}} (f₁ : Y ⟶ X₁.left) (f₂ : Y ⟶ X₂.left)
    (h : f₁ ⁻¹ᵁ U₁ = f₂ ⁻¹ᵁ U₂)
    (he : CommRingCat.ofHom e.toRingHom ≫ f₂.appLE U₂ (f₁ ⁻¹ᵁ U₁) h.le = f₁.app U₁)
    (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ U₁) (W : X₂.left.Opens) (hW : ⊤ ≤ f₂ ⁻¹ᵁ W) :
    ⊤ ≤ f₁ ⁻¹ᵁ sourceFor R X₁ X₂ U₁ U₂ hU₁ hU₂ e W := by
  intro y hy
  let v : (f₁ ⁻¹ᵁ U₁).toScheme := ⟨y,h₁ hy⟩
  let a := EquivReduction.Geometry.commonLift R X₁ U₁ f₁
  have hl : (EquivGeometry.left R X₁ U₁ hU₁) (a v) = f₁ y :=
    congrArg (fun k => k v) (EquivReduction.Geometry.commonLift_left R X₁ U₁ hU₁ f₁)
  have hr : (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) (a v) = f₂ y :=
    congrArg (fun k => k v) (EquivReduction.Geometry.commonLift_right R X₁ X₂ U₁ U₂ hU₂ e f₁ f₂ h he)
  refine ⟨a v, ?_, hl⟩
  change (EquivGeometry.right R X₁ X₂ U₁ U₂ hU₂ e) (a v) ∈ W
  rw [hr]
  exact hW hy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivNeighborhood.Geometry
