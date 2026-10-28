import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.PositiveNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ZeroNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology

/-! # Resolution Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionNaturality

noncomputable section

/-! Every augmented source-resolution comparison is natural in the original Ext groups. -/

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

include hφ in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (((IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).mapHomologicalComplex (.up ℕ)).map φ) i ≫
      (ResolutionCohomology.homologyIso R Y L κ hL i).hom =
        (ResolutionCohomology.homologyIso R Y K ι hK i).hom ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y i).map f := by
  cases i with
  | zero => exact ZeroNaturality.homology R Y ι κ φ f hφ
  | succ i => exact PositiveNaturality.naturality R Y ι κ hK hL φ f hφ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionNaturality
