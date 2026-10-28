/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingLocality

/-! # Tensor Pairing Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingGluing.SheafTensorLocalization

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

include hP in

lemma existsUnique_isPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    ∃! s : P.obj U, TensorPairingLocality.SheafTensorLocalization.IsPairingSection f g χ m n s := by
  have hT : Presieve.IsSheaf J (P.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J P.presheaf (forget _)).mp hP)
  have hSv : (Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n) ∈ J U.unop :=
    J.intersection_covering
      (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
      (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n)
  set Sv := Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n with hSvdef

  set x : Presieve.FamilyOfElements (P.presheaf ⋙ forget AddCommGrpCat) Sv.arrows :=
    fun V p hp => χ.app (Opposite.op V) (hp.1.choose ⊗ₜ hp.2.choose) with hxdef
  have hchoice : ∀ {V : C} (p : V ⟶ U.unop) (hp : Sv.arrows p),
      f.app (Opposite.op V) hp.1.choose = M₂.map p.op m ∧
        g.app (Opposite.op V) hp.2.choose = N₂.map p.op n :=
    fun p hp => ⟨hp.1.choose_spec, hp.2.choose_spec⟩

  have hx : x.Compatible := by
    intro V₁ V₂ W g₁ g₂ p₁ p₂ h₁ h₂ hcomm
    rw [hxdef]
    dsimp only
    erw [TensorPairingLocality.SheafTensorLocalization.chi_value, TensorPairingLocality.SheafTensorLocalization.chi_value]
    have hp₁ := hchoice p₁ h₁
    have hp₂ := hchoice p₂ h₂
    have hr₁ := TensorPairingLocality.SheafTensorLocalization.isPreimagePair_restrict g₁ p₁ _ _ hp₁.1 hp₁.2
    have hr₂ := TensorPairingLocality.SheafTensorLocalization.isPreimagePair_restrict g₂ p₂ _ _ hp₂.1 hp₂.2
    exact TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _
      (hr₁.1.trans (by rw [hcomm]; exact hr₂.1.symm))
      (hr₁.2.trans (by rw [hcomm]; exact hr₂.2.symm))

  have hamalg : TensorPairingLocality.SheafTensorLocalization.IsPairingSection f g χ m n ((hT Sv hSv).amalgamate x hx) := by
    intro V p a b ha hb
    apply hP.isSeparated _ _ (J.pullback_stable p hSv)
    intro W q hq
    have hglue := (hT Sv hSv).valid_glue hx (q ≫ p) hq
    erw [(TensorPairingLocality.SheafTensorLocalization.pom_map_comp P q p _).symm, hglue, hxdef]
    dsimp only
    erw [TensorPairingLocality.SheafTensorLocalization.chi_value]
    have hc := hchoice (q ≫ p) hq
    have hr := TensorPairingLocality.SheafTensorLocalization.isPreimagePair_restrict q p a b ha hb
    exact TensorPairingLocality.SheafTensorLocalization.chi_app_congr f g hP χ _ _ _ _ (hc.1.trans hr.1.symm) (hc.2.trans hr.2.symm)
  exact ⟨(hT Sv hSv).amalgamate x hx, hamalg,
    fun s hs => TensorPairingLocality.SheafTensorLocalization.isPairingSection_unique hP χ hs hamalg⟩

noncomputable def pairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    P.obj U :=
  (existsUnique_isPairingSection f g hP χ m n).exists.choose

lemma pairingSection_spec {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    TensorPairingLocality.SheafTensorLocalization.IsPairingSection f g χ m n (pairingSection f g hP χ m n) :=
  (existsUnique_isPairingSection f g hP χ m n).exists.choose_spec

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.TensorPairingGluing.SheafTensorLocalization
