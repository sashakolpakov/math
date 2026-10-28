import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOppositeNaturality

/-! # Chain Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainRefinement

noncomputable section

/-! Refinement of actual acyclic source resolutions induces the identity
on the original Ext groups. -/

open _root_.CategoryTheory Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (P Q : ChainComplex C ℕ) (β : Q ⟶ P)

def map : ChainCohomology.complex R Y P ⟶ ChainCohomology.complex R Y Q :=
  ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).mapHomologicalComplex (.up ℕ)).map
    ((HomologicalComplex.opFunctor C (.down ℕ)).map β.op)

variable {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] [QuasiIso η]
  (hβ : β ≫ ε = η)
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) Y (q + 1)))

include hβ in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (ChainRefinement.map R Y P Q β) i ≫
      (ChainCohomology.homologyIso R Y Q η hQ i).hom =
        (ChainCohomology.homologyIso R Y P ε hP i).hom := by
  let : QuasiIso (ChainResolutionOpposite.augmentation P ε) :=
    ChainResolutionOpposite.augmentation_quasiIso P ε
  let : QuasiIso (ChainResolutionOpposite.augmentation Q η) :=
    ChainResolutionOpposite.augmentation_quasiIso Q η
  have hb : β.f 0 ≫ ε.f 0 = η.f 0 ≫ 𝟙 Z :=
    (congrArg (fun a => a.f 0) hβ).trans (Category.comp_id _).symm
  have h := Contravariant.ResolutionNaturality.homology R Y
    (ChainResolutionOpposite.augmentation P ε) (ChainResolutionOpposite.augmentation Q η)
    hP hQ ((HomologicalComplex.opFunctor C (.down ℕ)).map β.op) (𝟙 (op Z))
    (ChainResolutionOppositeNaturality.augmentation P Q ε η β (𝟙 Z) hb) i
  exact h.trans ((congrArg (fun a =>
    (ChainCohomology.homologyIso R Y P ε hP i).hom ≫ a)
      ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y i).map_id (op Z))).trans
        (Category.comp_id _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainRefinement
