import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Ext Zero -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtZero.ExtZeroTransport

noncomputable section

/-! # Original degree-zero Ext transport in morphism coordinates -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {Z T : D} (src : Z ⟶ F.obj X) (tgt : F.obj Y ⟶ T)

theorem mk (a : X ⟶ Y) :
    (Ext.mk₀ src).comp (((Ext.mk₀ a).mapExactFunctor F).comp (Ext.mk₀ tgt) (add_zero 0)) (zero_add 0) =
      Ext.mk₀ (src ≫ F.map a ≫ tgt) := by
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]

theorem homEquiv (α : Ext.{z} X Y 0) :
    Ext.homEquiv₀ ((Ext.mk₀ src).comp ((α.mapExactFunctor F).comp (Ext.mk₀ tgt) (add_zero 0)) (zero_add 0)) =
      src ≫ F.map (Ext.homEquiv₀ α) ≫ tgt := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X Y).2 α
  rw [mk]
  have ha : Ext.homEquiv₀ (Ext.mk₀ a) = a := Ext.homEquiv₀.apply_symm_apply a
  rw [ha]
  exact Ext.homEquiv₀.apply_symm_apply _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtZero.ExtZeroTransport
