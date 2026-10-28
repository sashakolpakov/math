import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorShort
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Exact Functor Positive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorPositive

noncomputable section

/-! Positive-degree homology of actual source section complexes computes the original exact-functor Ext map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj (F.op.obj Z) ⟶
    (F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.op.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (((F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X a).unop (F.obj Y) (q + 1)))

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F.op (ComplexShape.up ℕ)) K

include hκ in
theorem homology (n : ℕ) : HomologicalComplex.homologyMap (ExactFunctorComplex.map F R Y K) (n + 1) ≫
    (Resolution.Comparison.positiveHomologyIso R (F.obj Y) L κ hL n).hom =
      (Resolution.Comparison.positiveHomologyIso R Y K ι hK n).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1) Z := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality (ExactFunctorComplex.map F R Y K) n
  have h₂ := ExactFunctorShort.short F R Y K ι κ hκ hK hL n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Resolution.Comparison.complex R Y K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorPositive
