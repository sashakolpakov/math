import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactResolutionTransport

/-! # Resolution Functor Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionFunctorNaturality

noncomputable section

/-! Balanced source-resolution cohomology is natural for exact functors
with unchanged transported coefficients. The coefficient-resolution map
is constructed, without an injective-preservation hypothesis. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)

theorem coefficientMap_id :
    ResolutionHom.TransportEdges.coefficientMap F R P Q β (𝟙 (F.obj Y)) =
      Acyclic.ChainFunctorNaturality.map F R Y P Q β := by
  apply HomologicalComplex.Hom.ext
  funext b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Ext.comp_mk₀_id _

variable {Z : C} {W : D} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ D).obj W) [QuasiIso ε] [QuasiIso η]
  (g : W ⟶ F.obj Z) (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)
  (I : InjectiveResolution Y) (I' : InjectiveResolution (F.obj Y))
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) (F.obj Y) (q + 1)))

include hβ in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (Acyclic.ChainFunctorNaturality.map F R Y P Q β) i ≫
      (ResolutionCohomology.homologyIso R Q η I' hQ i).hom =
        (ResolutionCohomology.homologyIso R P ε I hP i).hom ≫
          ResolutionHom.TransportCohomology.extMap F R g (𝟙 (F.obj Y)) i := by
  have h := ResolutionCohomology.naturality R P ε I hP F Q β η I' hQ
    (ExactResolutionTransport.map F (Iso.refl _) I I') g hβ (𝟙 _)
    (ExactResolutionTransport.augmentation_square F (Iso.refl _) I I') i
  exact (congrArg (fun a => HomologicalComplex.homologyMap a i ≫
    (ResolutionCohomology.homologyIso R Q η I' hQ i).hom)
      (coefficientMap_id F R Y P Q β).symm).trans h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionFunctorNaturality
