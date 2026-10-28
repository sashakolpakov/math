import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule

/-! # Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Transport

noncomputable section

/-! Actual mixed Hom bicomplex maps induced by an exact functor, a
source-resolution map, and a coefficient-complex map. No assertion about
injectivity of the transported coefficient complex is needed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R]
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)

abbrev rowMap (Y : C) := Acyclic.ChainFunctorNaturality.map F R Y P Q β

theorem rowMap_apply (Y : C) (a : ℕ) (x : Ext.{z} (P.X a) Y 0) :
    (rowMap F R P Q β Y).f a x =
      (Ext.mk₀ (β.f a)).comp (x.mapExactFunctor F) (zero_add 0) := rfl

theorem row_naturality {Y Y' : C} (g : Y ⟶ Y') :
    Acyclic.ChainCoefficientNaturality.complexMap R g P ≫ rowMap F R P Q β Y' =
      rowMap F R P Q β Y ≫ Acyclic.ChainCoefficientNaturality.complexMap R (F.map g) Q := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Ext.mk₀ (β.f a)).comp ((x.comp (Ext.mk₀ g) (add_zero 0)).mapExactFunctor F) (zero_add 0) =
    ((Ext.mk₀ (β.f a)).comp (x.mapExactFunctor F) (zero_add 0)).comp (Ext.mk₀ (F.map g)) (add_zero 0)
  have H := (Ext.mapExactFunctor_comp F x (Ext.mk₀ g) (add_zero 0)).trans
    (congrArg (fun e : Ext.{z} (F.obj Y) (F.obj Y') 0 =>
      (x.mapExactFunctor F).comp e (add_zero 0)) (Ext.mapExactFunctor_mk₀ F g))
  exact (congrArg (fun e : Ext.{z} (F.obj (P.X a)) (F.obj Y') 0 =>
    (Ext.mk₀ (β.f a)).comp e (zero_add 0)) H).trans
      (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (β.f a)) (x.mapExactFunctor F)
        (Ext.mk₀ (F.map g)) (zero_add 0)).symm

def rawMap (K : CochainComplex C ℕ) : Bicomplex.bicomplex R P K ⟶
    Bicomplex.bicomplex R Q ((F.mapHomologicalComplex (.up ℕ)).obj K) where
  f b := rowMap F R P Q β (K.X b)
  comm' b b' _ := (row_naturality F R P Q β (K.d b b')).symm

def map {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (γ : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) :
    Bicomplex.bicomplex R P K ⟶ Bicomplex.bicomplex R Q L :=
  rawMap F R P Q β K ≫ Bicomplex.map R Q γ

theorem map_apply {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (γ : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
    (b a : ℕ) (x : Ext.{z} (P.X a) (K.X b) 0) :
    ((Transport.map F R P Q β γ).f b).f a x =
      (Ext.mk₀ (β.f a)).comp
        ((x.mapExactFunctor F).comp (Ext.mk₀ (γ.f b)) (add_zero 0)) (zero_add 0) :=
  Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (β.f a)) (x.mapExactFunctor F)
    (Ext.mk₀ (γ.f b)) (zero_add 0)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Transport
