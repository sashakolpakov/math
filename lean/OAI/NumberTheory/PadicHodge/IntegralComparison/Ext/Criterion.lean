import Mathlib

/-! # Criterion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion.Comparison

noncomputable section

/-!
# IntegralComparison: a fixed-source criterion for comparison of Ext groups

An exact functor preserving injectives gives an Ext comparison at a fixed
source once its degree-zero Hom comparison is bijective for every target.
For an exact adjunction, it suffices that the counit at that source is an
isomorphism. These are general categorical lemmas; no crystalline or
étale comparison is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ Ext.mapExactFunctor_extClass

attribute [local instance] Ext.subsingleton_of_injective in
lemma bijective_of_hom_bijective [F.PreservesInjectiveObjects] (X : C)
    (h₀ : ∀ Y : C, Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)))
    (Y : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using h₀ Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map F).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n) (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ => Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ => Ext.covariant_sequence_exact₁ _ (hS.map F) y₁ (by subsingleton) rfl)

variable {L : D ⥤ C} (adj : L ⊣ F)

omit [Abelian C] [Abelian D] [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C] in
lemma hom_bijective_of_counit (X Y : C) [IsIso (adj.counit.app X)] :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  let e : (X ⟶ Y) ≃ (L.obj (F.obj X) ⟶ Y) :=
    Iso.homCongr (asIso (adj.counit.app X)).symm (Iso.refl Y)
  have he (g : X ⟶ Y) : e g = adj.counit.app X ≫ g := by simp [e]
  have hmap (g : X ⟶ Y) : (adj.homEquiv (F.obj X) Y) (e g) = F.map g := by
    rw [he, adj.homEquiv_naturality_right, ← adj.homEquiv_symm_id X]
    change (adj.homEquiv (F.obj X) X) ((adj.homEquiv (F.obj X) X).symm (𝟙 _)) ≫ F.map g = F.map g
    rw [Equiv.apply_symm_apply, Category.id_comp]
  have hbij := (adj.homEquiv (F.obj X) Y).bijective.comp e.bijective
  exact (show (fun g => (adj.homEquiv (F.obj X) Y) (e g)) = F.map from funext hmap) ▸ hbij

lemma bijective_of_counit [L.PreservesMonomorphisms] (X Y : C) [IsIso (adj.counit.app X)] (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact bijective_of_hom_bijective F X (fun Y => hom_bijective_of_counit F adj X Y) Y n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion.Comparison
