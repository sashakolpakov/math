import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearExt
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Ext Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ExtSections.SemilinearExtSections

noncomputable section

/-! # Actual Ext section maps for exact semilinear functors -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y)) (X : C)

def semilinearMap {Y : C} {Z : D} (b : F.obj Y ⟶ Z) (n : ℕ) :
    Ext.{z} X Y n →ₛₗ[σ] Ext.{z} (F.obj X) Z n :=
  ((Ext.mk₀ b).postcompOfLinear S (F.obj X) (add_zero n)).comp
    (NumberTheory.PadicHodge.PeriodInvariants.SemilinearExt.mapExt σ F hF X Y n)

def map {Y : C} {Z : D} (b : F.obj Y ⟶ Z) (n : ℕ) :
    ModuleCat.of R (Ext.{z} X Y n) ⟶
      (ModuleCat.restrictScalars σ).obj (ModuleCat.of S (Ext.{z} (F.obj X) Z n)) :=
  ModuleCat.ofHom (X := ModuleCat.of R (Ext.{z} X Y n))
    (Y := (ModuleCat.restrictScalars σ).obj (ModuleCat.of S (Ext.{z} (F.obj X) Z n))) {
    toFun := semilinearMap R S σ F hF X b n
    map_add' := map_add _
    map_smul' := (semilinearMap R S σ F hF X b n).map_smulₛₗ }

theorem map_apply {Y : C} {Z : D} (b : F.obj Y ⟶ Z) (n : ℕ) (α : Ext.{z} X Y n) :
    SemilinearExtSections.map R S σ F hF X b n α = (Ext.mk₀ b).postcomp (F.obj X) (add_zero n) (α.mapExactFunctor F) := rfl

theorem square {Y Y' : C} {Z Z' : D} (u : Y ⟶ Y') (v : Z ⟶ Z')
    (b : F.obj Y ⟶ Z) (c : F.obj Y' ⟶ Z') (h : F.map u ≫ c = b ≫ v) (n : ℕ) :
    (NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X n).map u ≫ SemilinearExtSections.map R S σ F hF X c n =
      SemilinearExtSections.map R S σ F hF X b n ≫
        (ModuleCat.restrictScalars σ).map ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) n).map v) := by
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
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℕ)).obj
        (((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) 0).mapHomologicalComplex (.up ℕ)).obj L) where
  f n := SemilinearExtSections.map R S σ F hF X (f.f n) 0
  comm' i j _ := (square R S σ F hF X (K.d i j) (L.d i j)
    (f.f i) (f.f j) (f.comm i j).symm 0).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ExtSections.SemilinearExtSections
