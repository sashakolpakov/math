import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv

/-! # Pointed Squares -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedSquares

noncomputable section

/-! The actual pointed equivalence preserves the original reduction
and section maps as morphisms of section rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ)
  (X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [Smooth X₁.hom] [Smooth X₂.hom]
  (Y : Over (Spec (CommRingCat.of k)))
  (f₁ : Y.left ⟶ X₁.left) (f₂ : Y.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y.hom X₁.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y.hom X₂.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U₁ : X₁.left.affineOpens) (U₂ : X₂.left.affineOpens)
  (h : f₁ ⁻¹ᵁ U₁.val = f₂ ⁻¹ᵁ U₂.val)
  (s₁ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₁.left)
  (hs₁ : s₁ ≫ X₁.hom = 𝟙 _)
  (s₂ : Spec (CommRingCat.of (Truncated.Witt.Ring p k n)) ⟶ X₂.left)
  (hs₂ : s₂ ≫ X₂.hom = 𝟙 _)
  (s₀ : Spec (CommRingCat.of k) ⟶ Y.left) (hs₀ : s₀ ≫ Y.hom = 𝟙 _)
  (hred₁ : s₀ ≫ f₁ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₁)
  (hred₂ : s₀ ≫ f₂ = Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n)) ≫ s₂)
  (h₁ : ⊤ ≤ s₁ ⁻¹ᵁ U₁.val) (h₂ : ⊤ ≤ s₂ ⁻¹ᵁ U₂.val)

local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedLocalEquiv.equiv
  p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂

theorem reduction_square :
    CommRingCat.ofHom (e).toRingHom ≫
        f₂.appLE U₂.val (f₁ ⁻¹ᵁ U₁.val) h.le = f₁.app U₁.val := by
  have hr : CommRingCat.ofHom (e).toRingHom ≫ f₂.app U₂.val =
      f₁.app U₁.val ≫ Y.left.presheaf.map (eqToHom h.symm).op := by
    ext a
    exact PointedLocalEquiv.reduction_equiv
      p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ a
  rw [Scheme.Hom.appLE, ← Category.assoc, hr, Category.assoc, ← Functor.map_comp]
  have hi : (eqToHom h.symm).op ≫ (homOfLE h.le).op = 𝟙 (op (f₁ ⁻¹ᵁ U₁.val)) :=
    Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]

theorem section_top_square :
    CommRingCat.ofHom (e).toRingHom ≫ s₂.appLE U₂.val ⊤ h₂ = s₁.appLE U₁.val ⊤ h₁ := by
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (Truncated.Witt.Ring p k n))).hom).1
  ext a
  exact PointedLocalEquiv.section_equiv
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂ a

theorem section_square :
    CommRingCat.ofHom (e).toRingHom ≫
        s₂.appLE U₂.val (s₁ ⁻¹ᵁ U₁.val)
          ((top_unique h₁).trans (top_unique h₂).symm).le = s₁.app U₁.val := by
  have : IsIso (homOfLE h₁) := by
    change IsIso (eqToHom (top_unique h₁).symm)
    infer_instance
  apply (cancel_mono
    ((Spec (CommRingCat.of (Truncated.Witt.Ring p k n))).presheaf.map (homOfLE h₁).op)).1
  rw [Category.assoc, Scheme.Hom.appLE_map]
  exact section_top_square
    p k n X₁ X₂ Y f₁ f₂ hp₁ hp₂ U₁ U₂ h s₁ hs₁ s₂ hs₂ s₀ hs₀ hred₁ hred₂ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedSquares
