/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingMorphisms

/-! # Tensor Localization Assembly -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalizationAssembly.SheafTensorLocalization

noncomputable section

/-! Tensor products preserve the class of maps inverted by actual module sheafification. -/

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (S ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}

theorem sheafificationW_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (hf : SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} α f) (hg : SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} α g) :
    SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} α (f ⊗ₘ g) := by
  obtain ⟨hfi, hfs⟩ := (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_iff_isLocallyBijective α f).mp hf
  obtain ⟨hgi, hgs⟩ := (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_iff_isLocallyBijective α g).mp hg
  have := hfi; have := hfs; have := hgi; have := hgs
  rw [SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_iff]
  apply isIso_of_coyoneda_map_bijective
  intro Y
  have hP : Presheaf.IsSheaf J
      ((SheafOfModules.forget R ⋙ restrictScalars α).obj Y).presheaf := Y.isSheaf
  have hΨ : Function.Bijective (fun (ψ : M₂ ⊗ N₂ ⟶
      (SheafOfModules.forget R ⋙ restrictScalars α).obj Y) => (f ⊗ₘ g) ≫ ψ) :=
    ⟨TensorLocalMaps.SheafTensorLocalization.tensorHom_precomp_injective f g hP, TensorPairingMorphisms.SheafTensorLocalization.tensorHom_precomp_surjective f g hP⟩
  have hconj : (fun (x : (sheafification.{u} α).obj (M₂ ⊗ N₂) ⟶ Y) =>
      (sheafification.{u} α).map (f ⊗ₘ g) ≫ x) =
      ⇑((sheafificationAdjunction α).homEquiv (M₁ ⊗ N₁) Y).symm ∘
        (fun ψ => (f ⊗ₘ g) ≫ ψ) ∘
          ⇑((sheafificationAdjunction α).homEquiv (M₂ ⊗ N₂) Y) := by
    funext x
    simp only [Function.comp_apply, Equiv.eq_symm_apply]
    exact (sheafificationAdjunction α).homEquiv_naturality_left (f ⊗ₘ g) x
  rw [hconj]
  exact ((sheafificationAdjunction α).homEquiv (M₁ ⊗ N₁) Y).symm.bijective.comp
    (hΨ.comp ((sheafificationAdjunction α).homEquiv (M₂ ⊗ N₂) Y).bijective)

lemma isLocallyInjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (hf : SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW α f) (hg : SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW α g) :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (f ⊗ₘ g)) :=
  ((SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW_iff_isLocallyBijective α (f ⊗ₘ g)).mp
    (sheafificationW_tensorHom α f g hf hg)).1

instance sheafificationW_isMultiplicative : (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} α).IsMultiplicative :=
  inferInstanceAs
    ((MorphismProperty.isomorphisms _).inverseImage (sheafification.{u} α)).IsMultiplicative

instance sheafificationW_isMonoidal : (SheafificationLocalEquivalences.SheafTensorLocalization.sheafificationW.{u} α).IsMonoidal :=
  MorphismProperty.IsMonoidal.mk' _ fun f g hf hg => sheafificationW_tensorHom α f g hf hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorLocalizationAssembly.SheafTensorLocalization
