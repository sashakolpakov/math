import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSource

/-! # Ext Pullback Comparison -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExtPullbackComparison

noncomputable section

/-! Exact restriction followed by source transport computes the original composite Ext pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R]
  (X : C) {X' : D} (f : X' ⟶ F.obj X)

def component (n : ℕ) (Y : C) : (ModuleFunctor.functor R X n).obj Y ⟶
    (ModuleFunctor.functor R X' n).obj (F.obj Y) :=
  ExactFunctorModule.component F R X n Y ≫ SourceModule.component R f n (F.obj Y)

theorem component_mk {Y : C} (a : X ⟶ Y) :
    component F R X f 0 Y (Ext.mk₀ a) = Ext.mk₀ (f ≫ F.map a) := by
  change (Ext.mk₀ f).comp ((Ext.mk₀ a).mapExactFunctor F) (zero_add 0) = _
  exact (congrArg (fun e : Ext.{z} (F.obj X) (F.obj Y) 0 =>
    (Ext.mk₀ f).comp e (zero_add 0)) (Ext.mapExactFunctor_mk₀ F a)).trans (Ext.mk₀_comp_mk₀ f (F.map a))

def complexMap (K : CochainComplex C ℕ) : Acyclic.Resolution.Comparison.complex R X K ⟶
    Acyclic.Resolution.Comparison.complex R X'
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) :=
  Acyclic.ExactFunctorComplex.map F R X K ≫
    SourceModule.complexMap R f ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

variable [F.PreservesInjectiveObjects] {Z : C} (I : InjectiveResolution Z)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (complexMap F R X f I.cocomplex) i ≫
    (InjectiveSectionCohomology.homologyIso R X' (ExactInjectiveResolution.map F I) i).hom =
      (InjectiveSectionCohomology.homologyIso R X I i).hom ≫ component F R X f i Z := by
  have h₁ := InjectiveExactFunctor.Comparison.homology F R X I i
  have h₂ := InjectiveSource.Comparison.homology R f (ExactInjectiveResolution.map F I) i
  have hm := HomologicalComplex.homologyMap_comp (Acyclic.ExactFunctorComplex.map F R X I.cocomplex)
    (SourceModule.complexMap R f ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) i
  exact (congrArg (fun a => a ≫
    (InjectiveSectionCohomology.homologyIso R X' (ExactInjectiveResolution.map F I) i).hom) hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => HomologicalComplex.homologyMap
          (Acyclic.ExactFunctorComplex.map F R X I.cocomplex) i ≫ a) h₂).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun a => a ≫ SourceModule.component R f i (F.obj Z)) h₁).trans
                (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExtPullbackComparison
