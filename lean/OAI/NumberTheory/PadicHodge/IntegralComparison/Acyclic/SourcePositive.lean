import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShort
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Source Positive -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourcePositive

noncomputable section

/-! The actual positive-degree resolution comparison is natural in the first argument of Ext. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hK' : ∀ a q, Subsingleton (Ext.{z} X' (K.X a) (q + 1)))

theorem homology (n : ℕ) : HomologicalComplex.homologyMap (IntegralComparison.Ext.SourceModule.complexMap R f K) (n + 1) ≫
    (Resolution.Comparison.positiveHomologyIso R X' K ι hK' n).hom =
      (Resolution.Comparison.positiveHomologyIso R X K ι hK n).hom ≫
        IntegralComparison.Ext.SourceModule.component R f (n + 1) Z := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality (IntegralComparison.Ext.SourceModule.complexMap R f K) n
  have h₂ := SourceShort.short R f K ι hK hK' n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Resolution.Comparison.shortHomologyIso R X' K ι hK' n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Resolution.Comparison.complex R X K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourcePositive
