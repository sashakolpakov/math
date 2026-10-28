import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainRefinement
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality

/-! # Resolution Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionRefinement

noncomputable section

/-! Refinement of source resolutions preserves the balanced comparison
with the original Ext groups. Both coefficient edges use the same actual
injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C] [EnoughInjectives C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (P Q : ChainComplex C ℕ) (β : Q ⟶ P)

def mappedSource : Q ⟶ ((𝟭 C).mapHomologicalComplex (.down ℕ)).obj P where
  f := β.f
  comm' i j _ := β.comm i j

theorem coefficientMap :
    ResolutionHom.TransportEdges.coefficientMap (𝟭 C) R P Q
      (mappedSource P Q β) (𝟙 Y) = Acyclic.ChainRefinement.map R Y P Q β := by
  apply HomologicalComplex.Hom.ext
  funext b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (ResolutionHom.TransportEdges.coefficientMap_apply (𝟭 C) R P Q
    (mappedSource P Q β) (𝟙 Y) b x).trans
      (congrArg ((Ext.mk₀ (β.f b)).comp · (zero_add 0))
        ((Ext.comp_mk₀_id _).trans (PeriodInvariants.ExtFunctoriality.mapExactFunctor_id x)))

theorem extMap (Z : C) (i : ℕ) :
    ResolutionHom.TransportCohomology.extMap (𝟭 C) R (𝟙 Z) (𝟙 Y) i =
      𝟙 (ModuleCat.of R (Ext.{z} Z Y i)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Ext.mk₀_id_comp _).trans
    ((Ext.comp_mk₀_id _).trans (PeriodInvariants.ExtFunctoriality.mapExactFunctor_id x))

variable {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] [QuasiIso η]
  (hβ : β ≫ ε = η) (I : InjectiveResolution Y)
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) Y (q + 1)))

include hβ in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (Acyclic.ChainRefinement.map R Y P Q β) i ≫
      (ResolutionCohomology.homologyIso R Q η I hQ i).hom =
        (ResolutionCohomology.homologyIso R P ε I hP i).hom := by
  let γ := (Functor.mapHomologicalComplexIdIso C (.up ℕ)).hom.app I.cocomplex
  have hb : (mappedSource P Q β).f 0 ≫ (𝟭 C).map (ε.f 0) = η.f 0 ≫ 𝟙 Z :=
    (congrArg (fun a => a.f 0) hβ).trans (Category.comp_id _).symm
  have hc : (𝟭 C).map (I.ι.f 0) ≫ γ.f 0 = 𝟙 Y ≫ I.ι.f 0 := by
    change I.ι.f 0 ≫ 𝟙 (I.cocomplex.X 0) = 𝟙 Y ≫ I.ι.f 0
    exact (Category.comp_id (show Y ⟶ I.cocomplex.X 0 from I.ι.f 0)).trans
      (Category.id_comp (show Y ⟶ I.cocomplex.X 0 from I.ι.f 0)).symm
  have hn := ResolutionCohomology.naturality R P ε I hP (𝟭 C) Q
    (mappedSource P Q β) η I hQ γ (𝟙 Z) hb (𝟙 Y) hc i
  rw [coefficientMap, extMap, Category.comp_id] at hn
  exact hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionRefinement
