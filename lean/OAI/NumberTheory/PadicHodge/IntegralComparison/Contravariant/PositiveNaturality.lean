import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShortNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Positive Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.PositiveNaturality

noncomputable section

/-!
# IntegralComparison: maps of actual acyclic source resolutions induce the original positive-degree Ext maps
-/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  {K L : CochainComplex Cᵒᵖ ℕ} {Z W : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) (κ : (CochainComplex.single₀ Cᵒᵖ).obj W ⟶ L)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop Y (q + 1)))
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ Cᵒᵖ).map f ≫ κ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

include hφ

theorem naturality (n : ℕ) : HomologicalComplex.homologyMap
    (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) (n + 1) ≫
      (Resolution.Comparison.positiveHomologyIso R Y L κ hL n).hom =
        (Resolution.Comparison.positiveHomologyIso R Y K ι hK n).hom ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y (n + 1)).map f := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality
    (((F).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n
  have h₂ := ShortNaturality.Comparison.short R Y ι κ hK hL φ f hφ n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Resolution.Comparison.shortHomologyIso R Y L κ hL n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Resolution.Comparison.complex R Y K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.PositiveNaturality
