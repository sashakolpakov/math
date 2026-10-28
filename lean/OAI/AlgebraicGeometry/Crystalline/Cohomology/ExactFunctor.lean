import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactFunctor.ExactFunctorExtSections

noncomputable section

/-! # The actual map on Ext sections induced by an exact linear functor -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C)

def map {Y : C} {Z : D} (b : F.obj Y ⟶ Z) (n : ℕ) :
    ModuleCat.of R (Ext.{z} X Y n) ⟶ ModuleCat.of R (Ext.{z} (F.obj X) Z n) :=
  ModuleCat.ofHom (((Ext.mk₀ b).postcompOfLinear R (F.obj X) (add_zero n)).comp
    (F.mapExtLinearMap R X Y n))

theorem map_apply {Y : C} {Z : D} (b : F.obj Y ⟶ Z) (n : ℕ) (α : Ext.{z} X Y n) :
    ExactFunctorExtSections.map R F X b n α = (Ext.mk₀ b).postcomp (F.obj X) (add_zero n) (α.mapExactFunctor F) := rfl

theorem square {Y Y' : C} {Z Z' : D} (u : Y ⟶ Y') (v : Z ⟶ Z')
    (b : F.obj Y ⟶ Z) (c : F.obj Y' ⟶ Z') (h : F.map u ≫ c = b ≫ v) (n : ℕ) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X n).map u ≫ ExactFunctorExtSections.map R F X c n =
      ExactFunctorExtSections.map R F X b n ≫ (NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) n).map v := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  change Ext.{z} X Y n at α
  change ((α.comp (Ext.mk₀ u) (add_zero n)).mapExactFunctor F).comp (Ext.mk₀ c) (add_zero n) =
    ((α.mapExactFunctor F).comp (Ext.mk₀ b) (add_zero n)).comp (Ext.mk₀ v) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  rw [h]

def complexMap {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 0).mapHomologicalComplex (.up ℕ)).obj L where
  f n := ExactFunctorExtSections.map R F X (f.f n) 0
  comm' i j _ := (square R F X (K.d i j) (L.d i j) (f.f i) (f.f j) (f.comm i j).symm 0).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactFunctor.ExactFunctorExtSections
