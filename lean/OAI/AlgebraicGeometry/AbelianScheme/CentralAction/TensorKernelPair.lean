import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Descent

/-! # Tensor Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TensorKernelPair.Construction

noncomputable section

/-! The kernel pair of a product map with an identity factor is the
product of that factor with the original kernel pair. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

def tensorKernelPairIso (H : C) {A B : C} (f : A ⟶ B) :
    pullback (𝟙 H ⊗ₘ f) (𝟙 H ⊗ₘ f) ≅ H ⊗ pullback f f := by
  let r := 𝟙 H ⊗ₘ f
  let p := pullback.fst r r
  let q := pullback.snd r r
  have hh : p ≫ fst H A = q ≫ fst H A := by
    have h := congrArg (fun a => a ≫ fst H B) (pullback.condition (f := r) (g := r))
    simpa [r, p, q] using h
  have hf : (p ≫ snd H A) ≫ f = (q ≫ snd H A) ≫ f := by
    have h := congrArg (fun a => a ≫ snd H B) (pullback.condition (f := r) (g := r))
    simpa [r, p, q] using h
  let a := lift (p ≫ fst H A) (pullback.lift (p ≫ snd H A) (q ≫ snd H A) hf)
  have hb : (𝟙 H ⊗ₘ pullback.fst f f) ≫ r = (𝟙 H ⊗ₘ pullback.snd f f) ≫ r := by
    simp only [r, tensorHom_comp_tensorHom, Category.id_comp, pullback.condition]
  let b := pullback.lift (𝟙 H ⊗ₘ pullback.fst f f) (𝟙 H ⊗ₘ pullback.snd f f) hb
  have hb₁ : b ≫ p = 𝟙 H ⊗ₘ pullback.fst f f := pullback.lift_fst _ _ _
  have hb₂ : b ≫ q = 𝟙 H ⊗ₘ pullback.snd f f := pullback.lift_snd _ _ _
  have ha₁ : a ≫ fst H (pullback f f) = p ≫ fst H A := lift_fst _ _
  have ha₂ : a ≫ snd H (pullback f f) =
      pullback.lift (p ≫ snd H A) (q ≫ snd H A) hf := lift_snd _ _
  have ha₂₁ : a ≫ snd H (pullback f f) ≫ pullback.fst f f = p ≫ snd H A := by
    rw [← Category.assoc, ha₂, pullback.lift_fst]
  have ha₂₂ : a ≫ snd H (pullback f f) ≫ pullback.snd f f = q ≫ snd H A := by
    rw [← Category.assoc, ha₂, pullback.lift_snd]
  have hap : a ≫ (𝟙 H ⊗ₘ pullback.fst f f) = p := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, Category.comp_id, ha₁]
    · rw [Category.assoc, tensorHom_snd, ha₂₁]
  have haq : a ≫ (𝟙 H ⊗ₘ pullback.snd f f) = q := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, Category.comp_id, ha₁, hh]
    · rw [Category.assoc, tensorHom_snd, ha₂₂]
  refine ⟨a, b, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp only [Category.id_comp]
    · change (a ≫ b) ≫ p = p
      rw [Category.assoc, hb₁, hap]
    · change (a ≫ b) ≫ q = q
      rw [Category.assoc, hb₂, haq]
  · apply CartesianMonoidalCategory.hom_ext <;> simp only [Category.id_comp]
    · change (b ≫ a) ≫ fst H (pullback f f) = fst H (pullback f f)
      rw [Category.assoc, ha₁, ← Category.assoc, hb₁, tensorHom_fst, Category.comp_id]
    · apply pullback.hom_ext
      · change ((b ≫ a) ≫ snd H (pullback f f)) ≫ pullback.fst f f =
          snd H (pullback f f) ≫ pullback.fst f f
        rw [Category.assoc, Category.assoc, ha₂₁, ← Category.assoc, hb₁, tensorHom_snd]
      · change ((b ≫ a) ≫ snd H (pullback f f)) ≫ pullback.snd f f =
          snd H (pullback f f) ≫ pullback.snd f f
        rw [Category.assoc, Category.assoc, ha₂₂, ← Category.assoc, hb₂, tensorHom_snd]

theorem tensorKernelPairIso_inv_fst (H : C) {A B : C} (f : A ⟶ B) :
    (tensorKernelPairIso H f).inv ≫ pullback.fst (𝟙 H ⊗ₘ f) (𝟙 H ⊗ₘ f) =
      𝟙 H ⊗ₘ pullback.fst f f := pullback.lift_fst _ _ _

theorem tensorKernelPairIso_inv_snd (H : C) {A B : C} (f : A ⟶ B) :
    (tensorKernelPairIso H f).inv ≫ pullback.snd (𝟙 H ⊗ₘ f) (𝟙 H ⊗ₘ f) =
      𝟙 H ⊗ₘ pullback.snd f f := pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.TensorKernelPair.Construction
