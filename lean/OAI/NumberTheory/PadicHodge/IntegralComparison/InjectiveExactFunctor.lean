import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorPositive
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution

/-! # Injective Exact Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctor.Comparison

noncomputable section

/-! Native exact restriction of injective resolutions induces the original Ext restriction in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  {Z : C} (I : InjectiveResolution Z)

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (Acyclic.ExactFunctorComplex.map F R X I.cocomplex) i ≫
      (InjectiveSectionCohomology.homologyIso R (F.obj X) (ExactInjectiveResolution.map F I) i).hom =
    (InjectiveSectionCohomology.homologyIso R X I i).hom ≫
      IntegralComparison.Ext.ExactFunctorModule.component F R X i Z := by
  let κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex :=
    (ExactInjectiveResolution.map F I).ι
  let : QuasiIso κ := (ExactInjectiveResolution.map F I).quasiIso
  cases i with
  | zero =>
    exact Acyclic.ExactFunctorZero.homology F R X I.cocomplex I.ι
      κ (ExactInjectiveResolution.map_ι_zero F I)
  | succ n =>
    exact Acyclic.ExactFunctorPositive.homology F R X I.cocomplex I.ι
      κ (ExactInjectiveResolution.map_ι_zero F I)
      (fun a q => Ext.subsingleton_of_injective X (I.cocomplex.X a) q)
      (fun a q => Ext.subsingleton_of_injective (F.obj X)
        ((ExactInjectiveResolution.map F I).cocomplex.X a) q) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctor.Comparison
