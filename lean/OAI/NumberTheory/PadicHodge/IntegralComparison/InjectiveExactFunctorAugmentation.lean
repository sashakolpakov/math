import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorPositive
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Injective Exact Functor Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctorAugmentation

noncomputable section

/-! Original Ext comparison for an exact functor whenever the particular restricted resolution remains injective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  {Z : C} (I : InjectiveResolution Z)
  (κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) [QuasiIso κ]
  (hI : ∀ a, Injective (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X a))

def resolution : InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective := hI
  ι := κ

theorem homology (hκ : κ.f 0 = F.map (I.ι.f 0)) (i : ℕ) :
    HomologicalComplex.homologyMap (Acyclic.ExactFunctorComplex.map F R X I.cocomplex) i ≫
      (InjectiveSectionCohomology.homologyIso R (F.obj X) (resolution F I κ hI) i).hom =
    (InjectiveSectionCohomology.homologyIso R X I i).hom ≫
      IntegralComparison.Ext.ExactFunctorModule.component F R X i Z := by
  let : ∀ a, Injective (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X a) := hI
  cases i with
  | zero => exact Acyclic.ExactFunctorZero.homology F R X I.cocomplex I.ι κ hκ
  | succ n =>
    exact Acyclic.ExactFunctorPositive.homology F R X I.cocomplex I.ι κ hκ
      (fun a q => Ext.subsingleton_of_injective X (I.cocomplex.X a) q)
      (fun a q => Ext.subsingleton_of_injective (F.obj X)
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X a) q) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctorAugmentation
