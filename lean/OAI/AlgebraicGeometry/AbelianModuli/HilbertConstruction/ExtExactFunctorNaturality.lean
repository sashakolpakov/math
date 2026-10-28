import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Ext Exact Functor Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorNaturality

noncomputable section

/-! Maps on Ext induced by exact functors commute with natural transformations. The proof uses injective effacement in the source category and actual short-exact extension classes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem ext_mapExactFunctor_naturality (a : F ⟶ G) (X Y : C) (n : ℕ) (x : Ext X Y n) :
    (Ext.mk₀ (a.app X)).comp (x.mapExactFunctor G) (zero_add n) =
      (x.mapExactFunctor F).comp (Ext.mk₀ (a.app Y)) (add_zero n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨b, rfl⟩ := Ext.addEquiv₀.symm.surjective x
    change (Ext.mk₀ (a.app X)).comp ((Ext.mk₀ b).mapExactFunctor G) (zero_add 0) =
      ((Ext.mk₀ b).mapExactFunctor F).comp (Ext.mk₀ (a.app Y)) (add_zero 0)
    rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
    exact congrArg Ext.mk₀ (a.naturality b).symm
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact I.f }
    have : Injective S.X₂ := I.injective
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    have hd : (hS.extClass.mapExactFunctor F).comp (Ext.mk₀ (a.app Y)) (add_zero 1) =
        (Ext.mk₀ (a.app S.X₃)).comp (hS.extClass.mapExactFunctor G) (zero_add 1) := by
      rw [Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass]
      exact (hS.map F).extClass_naturality (hS.map G) (S.mapNatTrans a)
    rw [← hz, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp]
    calc
      (Ext.mk₀ (a.app X)).comp
          ((z.mapExactFunctor G).comp (hS.extClass.mapExactFunctor G) rfl) (zero_add (n + 1)) =
          ((Ext.mk₀ (a.app X)).comp (z.mapExactFunctor G) (zero_add n)).comp
            (hS.extClass.mapExactFunctor G) rfl :=
        (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
      _ = ((z.mapExactFunctor F).comp (Ext.mk₀ (a.app S.X₃)) (add_zero n)).comp
          (hS.extClass.mapExactFunctor G) rfl := by rw [ih]
      _ = (z.mapExactFunctor F).comp
          ((Ext.mk₀ (a.app S.X₃)).comp (hS.extClass.mapExactFunctor G) (zero_add 1)) rfl :=
        Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
      _ = (z.mapExactFunctor F).comp
          ((hS.extClass.mapExactFunctor F).comp (Ext.mk₀ (a.app Y)) (add_zero 1)) rfl := by
        rw [← hd]
      _ = ((z.mapExactFunctor F).comp (hS.extClass.mapExactFunctor F) rfl).comp
          (Ext.mk₀ (a.app Y)) (add_zero (n + 1)) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtExactFunctorNaturality
