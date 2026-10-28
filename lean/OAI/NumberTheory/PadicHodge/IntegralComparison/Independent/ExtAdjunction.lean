import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion

/-! # Ext Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtAdjunction

noncomputable section

/-! The canonical Ext adjunction from exactness and preservation of injectives. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe e65eau e65eav e65eaw e65eau' e65eav' e65eaw'

variable {C : Type e65eau} [Category.{e65eav} C] [Abelian C]
  {D : Type e65eau'} [Category.{e65eav'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{e65eaw} C] [HasExt.{e65eaw'} D]
  {L : D ⥤ C} (adj : L ⊣ F)

def comparison (X : D) (Y : C) (n : ℕ) :
    Ext.{e65eaw} (L.obj X) Y n →+ Ext.{e65eaw'} X (F.obj Y) n :=
  ((Ext.mk₀ (adj.unit.app X)).precomp (F.obj Y) (Nat.zero_add n)).comp
    (F.mapExtAddHom (L.obj X) Y n)

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

theorem comparison_mk₀ (X : D) (Y : C) (f : L.obj X ⟶ Y) :
    comparison F adj X Y 0 (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv X Y f) := by
  simp [comparison, Adjunction.homEquiv_apply]

theorem comparison_comp (X : D) {Y Z : C} {n m k : ℕ}
    (a : Ext.{e65eaw} (L.obj X) Y n) (b : Ext.{e65eaw} Y Z m) (hnm : n + m = k) :
    comparison F adj X Z k (a.comp b hnm) =
      (comparison F adj X Y n a).comp (b.mapExactFunctor F) hnm := by
  change (Ext.mk₀ (adj.unit.app X)).comp ((a.comp b hnm).mapExactFunctor F) (Nat.zero_add k) =
    ((Ext.mk₀ (adj.unit.app X)).comp (a.mapExactFunctor F) (Nat.zero_add n)).comp
      (b.mapExactFunctor F) hnm
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ (adj.unit.app X)) (a.mapExactFunctor F)
    (b.mapExactFunctor F) (Nat.zero_add n) hnm (by omega)).symm

attribute [local simp] comparison_mk₀ comparison_comp

theorem bijective_zero (X : D) (Y : C) :
    Function.Bijective (comparison F adj X Y 0) := by
  constructor
  · intro a b hab
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (L.obj X) Y).surjective a
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (L.obj X) Y).surjective b
    rw [comparison_mk₀, comparison_mk₀] at hab
    exact congrArg Ext.mk₀ ((adj.homEquiv X Y).injective
      ((Ext.mk₀_bijective X (F.obj Y)).injective hab))
  · intro b
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective X (F.obj Y)).surjective b
    refine ⟨Ext.mk₀ ((adj.homEquiv X Y).symm g), ?_⟩
    rw [comparison_mk₀, Equiv.apply_symm_apply]

variable [EnoughInjectives C] [F.PreservesInjectiveObjects]

attribute [local instance] Ext.subsingleton_of_injective in
theorem bijective (X : D) (Y : C) (n : ℕ) :
    Function.Bijective (comparison F adj X Y n) := by
  induction n generalizing Y with
  | zero => exact bijective_zero F adj X Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map F).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (comparison F adj X S.X₂ n) (comparison F adj X S.X₃ n)
      (comparison F adj X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (L.obj X) hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ => Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ => Ext.covariant_sequence_exact₁ _ (hS.map F) y₁ (by subsingleton) rfl)

def equivalence (X : D) (Y : C) (n : ℕ) :
    Ext.{e65eaw} (L.obj X) Y n ≃+ Ext.{e65eaw'} X (F.obj Y) n :=
  AddEquiv.ofBijective (comparison F adj X Y n) (bijective F adj X Y n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtAdjunction
