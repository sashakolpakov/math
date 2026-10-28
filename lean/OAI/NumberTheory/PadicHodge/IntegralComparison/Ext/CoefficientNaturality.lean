import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.CoefficientNaturality

noncomputable section

/-! Postcomposition in the actual coefficient object commutes with the
source-resolution connecting maps and their short-complex homology data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {Y Y' : C} (g : Y ⟶ Y')

def component (i : ℕ) (X : C) :
    ModuleCat.of R (Ext.{z} X Y i) ⟶ ModuleCat.of R (Ext.{z} X Y' i) :=
  ModuleCat.ofHom ((Ext.mk₀ g).postcompOfLinear R X (Nat.add_zero i))

theorem naturality (i : ℕ) {X X' : Cᵒᵖ} (f : X ⟶ X') :
    (ContravariantModuleFunctor.functor R Y i).map f ≫ component R g i X'.unop =
      component R g i X.unop ≫ (ContravariantModuleFunctor.functor R Y' i).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ f.unop) α (Ext.mk₀ g) (zero_add i)

def transformation (i : ℕ) :
    ContravariantModuleFunctor.functor R Y i ⟶
      ContravariantModuleFunctor.functor R Y' i where
  app X := component R g i X.unop
  naturality _ _ f := CoefficientNaturality.naturality R g i f

def shortMap (i : ℕ) (T : ShortComplex Cᵒᵖ) :
    T.map (ContravariantModuleFunctor.functor R Y i) ⟶
      T.map (ContravariantModuleFunctor.functor R Y' i) where
  τ₁ := component R g i T.X₁.unop
  τ₂ := component R g i T.X₂.unop
  τ₃ := component R g i T.X₃.unop
  comm₁₂ := (CoefficientNaturality.naturality R g i T.f).symm
  comm₂₃ := (CoefficientNaturality.naturality R g i T.g).symm

def complexMap (K : CochainComplex Cᵒᵖ ℕ) :
    Contravariant.Resolution.Comparison.complex R Y K ⟶
      Contravariant.Resolution.Comparison.complex R Y' K where
  f i := component R g 0 (K.X i).unop
  comm' i j _ := (CoefficientNaturality.naturality R g 0 (K.d i j)).symm

theorem complexMap_differential (K : CochainComplex Cᵒᵖ ℕ) (n : ℕ) :
    Augmented.ResolutionCycleMaps.differential (complexMap R g K) n =
      shortMap R g 0 (Augmented.ResolutionCycles.differentialSequence K n) := rfl

theorem connecting {S : ShortComplex C} (hS : S.ShortExact) (m : ℕ)
    (α : Ext.{z} S.X₁ Y m) :
    SourceDimensionShift.connecting hS Y' m
      ((Ext.mk₀ g).postcomp S.X₁ (Nat.add_zero m) α) =
      (Ext.mk₀ g).postcomp S.X₃ (Nat.add_zero (m + 1))
        (SourceDimensionShift.connecting hS Y m α) :=
  (Ext.comp_assoc_of_third_deg_zero hS.extClass α (Ext.mk₀ g) (Nat.add_comm 1 m)).symm

theorem connecting_zero {S : ShortComplex Cᵒᵖ} (hS : S.ShortExact) :
    component R g 0 S.X₃.unop ≫ SourceZeroCokernel.connecting R Y' hS =
      SourceZeroCokernel.connecting R Y hS ≫ component R g 1 S.X₁.unop := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact connecting g hS.unop 0 α

variable (T : ShortComplex Cᵒᵖ) {A : Cᵒᵖ} (a : A ⟶ T.X₁)
  (ha : a ≫ T.toCycles = 0) (hS : (ShortComplex.mk a T.toCycles ha).ShortExact)
  [Subsingleton (Ext.{z} T.X₁.unop Y 1)] [Subsingleton (Ext.{z} T.X₁.unop Y' 1)]

local notation "dY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData.data R Y T a ha hS
local notation "dY'" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData.data R Y' T a ha hS

def homologyData : ShortComplex.LeftHomologyMapData (shortMap R g 0 T) dY dY' where
  φK := component R g 0 T.cycles.unop
  φH := component R g 1 A.unop
  commi := (CoefficientNaturality.naturality R g 0 T.iCycles).symm
  commf' := by
    have hY := SourceZeroKernels.cycleKernel_lift R Y T
    have hY' := SourceZeroKernels.cycleKernel_lift R Y' T
    exact (congrArg (fun f => f ≫ component R g 0 T.cycles.unop) hY).trans
      ((CoefficientNaturality.naturality R g 0 T.toCycles).trans
        (congrArg (fun f => component R g 0 T.X₁.unop ≫ f) hY'.symm))
  commπ := (connecting_zero R g hS).symm

theorem short_homology : ShortComplex.homologyMap (shortMap R g 0 T) ≫
    (Contravariant.ResolutionHomologyData.homologyIso R Y' T a ha hS).hom =
      (Contravariant.ResolutionHomologyData.homologyIso R Y T a ha hS).hom ≫
        component R g 1 A.unop :=
  (homologyData R g T a ha hS).homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.CoefficientNaturality
