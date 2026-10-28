import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorShort
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Exact Functor Positive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorPositive

noncomputable section

/-! Positive-degree homology of actual section complexes computes the original exact-functor Ext map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (F.obj X)
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X a) (q + 1)))

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

include hκ in
theorem homology (n : ℕ) : HomologicalComplex.homologyMap (ExactFunctorComplex.map F R X K) (n + 1) ≫
    (Resolution.Comparison.positiveHomologyIso R (F.obj X) L κ hL n).hom =
      (Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom ≫
        IntegralComparison.Ext.ExactFunctorModule.component F R X (n + 1) Z := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality (ExactFunctorComplex.map F R X K) n
  have h₂ := ExactFunctorShort.short F R X K ι κ hκ hK hL n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Resolution.Comparison.shortHomologyIso R (F.obj X) L κ hL n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Resolution.Comparison.complex R X K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorPositive
