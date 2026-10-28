import Mathlib

/-! # Ext Functoriality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality

noncomputable section

/-!
# Functoriality of the actual Ext transport maps

Dimension shifting proves identity, composition, and naturality for Ext maps
induced by exact functors. These laws are needed for the geometric Galois action
on rational pro-étale cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w₁ w₂ w₃

attribute [local instance] Ext.subsingleton_of_injective

section Identity

variable {C : Type*} [Category C] [Abelian C] [HasExt.{w₁} C] [EnoughInjectives C]

theorem mapExactFunctor_id {X Y : C} {n : ℕ} (α : Ext X Y n) :
    α.mapExactFunctor (𝟭 C) = α := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective α
    rw [Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ X hS α (by subsingleton) rfl
    rw [← hβ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

end Identity

section Composition

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E] [EnoughInjectives C]
variable (F : C ⥤ D) (G : D ⥤ E)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem mapExactFunctor_compFunctor {X Y : C} {n : ℕ} (α : Ext X Y n) :
    α.mapExactFunctor (F ⋙ G) = (α.mapExactFunctor F).mapExactFunctor G := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective α
    simp only [Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ X hS α (by subsingleton) rfl
    have hδ : hS.extClass.mapExactFunctor (F ⋙ G) =
        (hS.extClass.mapExactFunctor F).mapExactFunctor G := by
      have h₀ : (hS.map_of_exact (F ⋙ G)).extClass =
          ((hS.map_of_exact F).map_of_exact G).extClass := rfl
      exact (Ext.mapExactFunctor_extClass (F ⋙ G) hS).trans
        (h₀.trans ((Ext.mapExactFunctor_extClass G (hS.map_of_exact F)).symm.trans
          (congrArg (Ext.mapExactFunctor G) (Ext.mapExactFunctor_extClass F hS).symm)))
    rw [← hβ]
    calc
      (β.comp hS.extClass rfl).mapExactFunctor (F ⋙ G) =
          (β.mapExactFunctor (F ⋙ G)).comp (hS.extClass.mapExactFunctor (F ⋙ G)) rfl :=
        Ext.mapExactFunctor_comp _ _ _ _
      _ = ((β.mapExactFunctor F).mapExactFunctor G).comp
          ((hS.extClass.mapExactFunctor F).mapExactFunctor G) rfl :=
        congrArg₂ (fun b d => b.comp d rfl) (ih β) hδ
      _ = ((β.mapExactFunctor F).comp (hS.extClass.mapExactFunctor F) rfl).mapExactFunctor G :=
        (Ext.mapExactFunctor_comp G _ _ _).symm
      _ = ((β.comp hS.extClass rfl).mapExactFunctor F).mapExactFunctor G :=
        congrArg (Ext.mapExactFunctor G) (Ext.mapExactFunctor_comp F β hS.extClass rfl).symm

end Composition

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D] [EnoughInjectives C]
variable {F G : C ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem mapExactFunctor_naturality (η : F ⟶ G) {X Y : C} {n : ℕ} (α : Ext X Y n) :
    (α.mapExactFunctor F).comp (Ext.mk₀ (η.app Y)) (Nat.add_zero n) =
      (Ext.mk₀ (η.app X)).comp (α.mapExactFunctor G) (Nat.zero_add n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective α
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    exact congrArg Ext.mk₀ (η.naturality f)
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have : Injective S.X₂ := I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨β, hβ⟩ := Ext.covariant_sequence_exact₁ X hS α (by subsingleton) rfl
    have hδ : (hS.extClass.mapExactFunctor F).comp (Ext.mk₀ (η.app Y)) (Nat.add_zero 1) =
        (Ext.mk₀ (η.app S.X₃)).comp (hS.extClass.mapExactFunctor G) (Nat.zero_add 1) := by
      have h₁ := congrArg
        (fun d => d.comp (Ext.mk₀ (η.app Y)) (Nat.add_zero 1))
        (Ext.mapExactFunctor_extClass F hS)
      have h₂ := (hS.map_of_exact F).extClass_naturality (hS.map_of_exact G) (S.mapNatTrans η)
      have h₃ := congrArg
        (fun d => (Ext.mk₀ (η.app S.X₃)).comp d (Nat.zero_add 1))
        (Ext.mapExactFunctor_extClass G hS).symm
      exact h₁.trans (h₂.trans h₃)
    rw [← hβ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
      Ext.comp_assoc_of_third_deg_zero, hδ, ← Ext.comp_assoc_of_second_deg_zero, ih]
    exact Ext.comp_assoc (Ext.mk₀ (η.app X)) (β.mapExactFunctor G)
      (hS.extClass.mapExactFunctor G) (Nat.zero_add n) rfl (by omega)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality
