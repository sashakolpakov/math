/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingBilinearity

/-! # Tensor Pairing Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingMorphisms.SheafTensorLocalization

noncomputable section

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
  {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (hP : Presheaf.IsSheaf J P.presheaf) (χ : M₁ ⊗ N₁ ⟶ P)

noncomputable def pairingLinear (U : Cᵒᵖ) :
    ↑(M₂.obj U) →ₗ[↑(S.obj U)]
      (↑(N₂.obj U) →ₗ[↑(S.obj U)] ↑(P.obj U)) where
  toFun m :=
    { toFun := TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ m
      map_add' := TensorPairingBilinearity.SheafTensorLocalization.pairingSection_add_right f g hP χ m
      map_smul' := fun r n => TensorPairingBilinearity.SheafTensorLocalization.pairingSection_smul_right f g hP χ r m n }
  map_add' m m' := LinearMap.ext (fun n => TensorPairingBilinearity.SheafTensorLocalization.pairingSection_add_left f g hP χ m m' n)
  map_smul' r m := LinearMap.ext (fun n => TensorPairingBilinearity.SheafTensorLocalization.pairingSection_smul_left f g hP χ r m n)

noncomputable def gluedHom : M₂ ⊗ N₂ ⟶ P where
  app U := ModuleCat.ofHom (TensorProduct.lift (pairingLinear f g hP χ U))
  naturality {U V} p := by
    ext t
    show TensorProduct.lift (pairingLinear f g hP χ V) ((M₂ ⊗ N₂).map p t) =
      P.map p (TensorProduct.lift (pairingLinear f g hP χ U) t)
    induction t using TensorProduct.inductionOn with
    | tmul m n =>
        have h2 : (M₂ ⊗ N₂).map p (m ⊗ₜ n) =
            (show ↑(M₂.obj V) from M₂.map p m) ⊗ₜ
              (show ↑(N₂.obj V) from N₂.map p n) := by
          erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
          rfl
        rw [h2]
        exact (TensorPairingBilinearity.SheafTensorLocalization.pairingSection_map f g hP χ p.unop m n).symm
    | add t₁ t₂ h₁ h₂ =>
        erw [map_add, map_add]
        exact (congrArg₂ (· + ·) h₁ h₂).trans
          ((map_add ((P.presheaf.map p).hom)
            (TensorProduct.lift (pairingLinear f g hP χ U) t₁)
            (TensorProduct.lift (pairingLinear f g hP χ U) t₂)).symm.trans
              (congrArg (P.map p)
                (map_add (TensorProduct.lift (pairingLinear f g hP χ U)) t₁ t₂).symm))

include hP in
lemma gluedHom_fac : (f ⊗ₘ g) ≫ gluedHom f g hP χ = χ := by
  refine hom_ext (fun U => ?_)
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      show TensorProduct.lift (pairingLinear f g hP χ U)
        ((f ⊗ₘ g).app U (a ⊗ₜ b)) = χ.app U (a ⊗ₜ b)
      have h1 : (f ⊗ₘ g).app U (a ⊗ₜ b) = f.app U a ⊗ₜ g.app U b := by
        erw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
      rw [h1]
      have h2 : TensorProduct.lift (pairingLinear f g hP χ U)
          (f.app U a ⊗ₜ g.app U b) =
            TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ (f.app U a) (g.app U b) := rfl
      rw [h2]
      have hida : f.app U a = M₂.map (𝟙 U.unop).op (f.app U a) :=
        ((CategoryTheory.congr_fun (M₂.presheaf.map_id U) (f.app U a)).trans rfl).symm
      have hidb : g.app U b = N₂.map (𝟙 U.unop).op (g.app U b) :=
        ((CategoryTheory.congr_fun (N₂.presheaf.map_id U) (g.app U b)).trans rfl).symm
      have h4 := TensorPairingGluing.SheafTensorLocalization.pairingSection_spec f g hP χ (f.app U a) (g.app U b)
        (𝟙 U.unop) a b hida hidb
      refine Eq.trans ?_ h4
      exact ((CategoryTheory.congr_fun (P.presheaf.map_id U)
        (TensorPairingGluing.SheafTensorLocalization.pairingSection f g hP χ (f.app U a) (g.app U b))).trans rfl).symm
  | add t₁ t₂ h₁ h₂ =>
      erw [map_add, map_add]
      rw [h₁, h₂]

include hP in

theorem tensorHom_precomp_surjective :
    Function.Surjective (fun (ψ : M₂ ⊗ N₂ ⟶ P) => (f ⊗ₘ g) ≫ ψ) :=
  fun χ => ⟨gluedHom f g hP χ, gluedHom_fac f g hP χ⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingMorphisms.SheafTensorLocalization
