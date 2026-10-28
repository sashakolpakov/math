import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Source Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule

noncomputable section

/-! Precomposition acts naturally on original Ext modules, connecting maps, and section complexes. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)

def component (n : ℕ) (Y : C) : (ModuleFunctor.functor R X n).obj Y ⟶
    (ModuleFunctor.functor R X' n).obj Y :=
  ModuleCat.ofHom ((Ext.mk₀ f).precompOfLinear R Y (zero_add n))

theorem naturality (n : ℕ) {Y Z : C} (g : Y ⟶ Z) :
    (ModuleFunctor.functor R X n).map g ≫ component R f n Z =
      component R f n Y ≫ (ModuleFunctor.functor R X' n).map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ f) α (Ext.mk₀ g) (zero_add n)).symm

def transformation (n : ℕ) : ModuleFunctor.functor R X n ⟶ ModuleFunctor.functor R X' n where
  app := component R f n
  naturality _ _ g := SourceModule.naturality R f n g

def shortMap (n : ℕ) (T : ShortComplex C) : T.map (ModuleFunctor.functor R X n) ⟶
    T.map (ModuleFunctor.functor R X' n) where
  τ₁ := component R f n T.X₁
  τ₂ := component R f n T.X₂
  τ₃ := component R f n T.X₃
  comm₁₂ := (SourceModule.naturality R f n T.f).symm
  comm₂₃ := (SourceModule.naturality R f n T.g).symm

theorem connecting {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) (α : Ext.{z} X S.X₃ n) :
    DimensionShift.connecting X' hS n (component R f n S.X₃ α) =
      component R f (n + 1) S.X₁ (DimensionShift.connecting X hS n α) :=
  Ext.comp_assoc (Ext.mk₀ f) α hS.extClass (zero_add n) rfl (by omega)

def complexMap (K : CochainComplex C ℕ) : Acyclic.Resolution.Comparison.complex R X K ⟶
    Acyclic.Resolution.Comparison.complex R X' K where
  f i := component R f 0 (K.X i)
  comm' i j _ := (SourceModule.naturality R f 0 (K.d i j)).symm

theorem differential (K : CochainComplex C ℕ) (n : ℕ) :
    Augmented.ResolutionCycleMaps.differential (complexMap R f K) n =
      shortMap R f 0 (Augmented.ResolutionCycles.differentialSequence K n) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule
