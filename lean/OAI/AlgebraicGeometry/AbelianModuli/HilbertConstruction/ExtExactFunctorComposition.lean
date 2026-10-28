import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorNaturality

/-! # Ext Exact Functor Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorComposition

noncomputable section

/-! Exact-functor maps on Ext preserve the identity and composition of functors. Injective effacement proves the laws in all degrees. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
universe u v u' v' u'' v'' w w' w''

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E]

omit [EnoughInjectives C] in
theorem ext_extClass_mapExactFunctor_comp
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {S : ShortComplex C} (hS : S.ShortExact) :
    (hS.extClass.mapExactFunctor F).mapExactFunctor G =
      hS.extClass.mapExactFunctor (F ⋙ G) := by
  let x : Ext (F.obj S.X₃) (F.obj S.X₁) 1 := (hS.map_of_exact F).extClass
  have hx : hS.extClass.mapExactFunctor F = x := Ext.mapExactFunctor_extClass F hS
  have hy : x.mapExactFunctor G = ((hS.map_of_exact F).map_of_exact G).extClass :=
    Ext.mapExactFunctor_extClass G (hS.map_of_exact F)
  exact (congrArg (fun z : Ext (F.obj S.X₃) (F.obj S.X₁) 1 =>
    z.mapExactFunctor G) hx).trans
      (hy.trans (Ext.mapExactFunctor_extClass (F ⋙ G) hS).symm)

theorem ext_mapExactFunctor_id (X Y : C) (n : ℕ) (x : Ext X Y n) :
    x.mapExactFunctor (𝟭 C) = x := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨a, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    change (Ext.mk₀ a).mapExactFunctor (𝟭 C) = Ext.mk₀ a
    rw [Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
    have : Injective S.X₂ := I.injective
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    rw [← hz, Ext.mapExactFunctor_comp, ih, Ext.mapExactFunctor_extClass]

theorem ext_mapExactFunctor_comp
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (X Y : C) (n : ℕ) (x : Ext X Y n) :
    (x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨a, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    change ((Ext.mk₀ a).mapExactFunctor F).mapExactFunctor G =
      (Ext.mk₀ a).mapExactFunctor (F ⋙ G)
    rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
    have : Injective S.X₂ := I.injective
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    rw [← hz]
    simp only [Ext.mapExactFunctor_comp]
    rw [ih]
    exact congrArg (fun b : Ext ((F ⋙ G).obj S.X₃) ((F ⋙ G).obj Y) 1 =>
      (z.mapExactFunctor (F ⋙ G)).comp b (rfl : n + 1 = n + 1))
        (ext_extClass_mapExactFunctor_comp F G hS)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorComposition
