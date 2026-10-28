import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ZeroNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.PositiveNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # To Injective -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjective.Comparison

noncomputable section

/-! The canonical dimension-shift comparison agrees with every augmentation-preserving map to an actual injective resolution. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι] (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))

def homologyIso (i : ℕ) : (Resolution.Comparison.complex R X K).homology i ≅
    ModuleCat.of R (Ext.{z} X Z i) := by
  cases i with
  | zero => exact ResolutionZero.Comparison.homologyIso R X K ι
  | succ n => exact Resolution.Comparison.positiveHomologyIso R X K ι hK n

variable (I : InjectiveResolution Z) (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι)

include hφ in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (((IntegralComparison.Ext.ModuleFunctor.functor R X 0).mapHomologicalComplex (.up ℕ)).map φ) i ≫
      (InjectiveSectionCohomology.homologyIso R X I i).hom = (homologyIso R X K ι hK i).hom := by
  have ha : ι ≫ φ = (CochainComplex.single₀ C).map (𝟙 Z) ≫ I.ι :=
    hφ.trans ((congrArg (fun a => a ≫ I.ι) ((CochainComplex.single₀ C).map_id Z)).trans (Category.id_comp _)).symm
  cases i with
  | zero =>
    have h := ZeroNaturality.homology R X ι I.ι φ (𝟙 Z) ha
    exact h.trans ((congrArg (fun a => (homologyIso R X K ι hK 0).hom ≫ a)
      ((IntegralComparison.Ext.ModuleFunctor.functor R X 0).map_id Z)).trans (Category.comp_id _))
  | succ n =>
    have h := PositiveNaturality.naturality R X ι I.ι hK
      (fun a q => Ext.subsingleton_of_injective X (I.cocomplex.X a) q) φ (𝟙 Z) ha n
    exact h.trans ((congrArg (fun a => (homologyIso R X K ι hK (n + 1)).hom ≫ a)
      ((IntegralComparison.Ext.ModuleFunctor.functor R X (n + 1)).map_id Z)).trans (Category.comp_id _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ToInjective.Comparison
