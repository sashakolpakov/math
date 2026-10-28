import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality

/-! # Chain Mixed Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainMixedNaturality

noncomputable section

/-! Exact-functor and source naturality of original Ext, requiring only the
two genuine augmented resolutions to be acyclic for their coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)
  {Z : C} {W : D} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ D).obj W) [QuasiIso ε] [QuasiIso η]
  (g : W ⟶ F.obj Z) (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) (F.obj Y) (q + 1)))

include hβ in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap
    (ChainFunctorNaturality.map F R Y P Q β) i ≫
      (ChainCohomology.homologyIso R (F.obj Y) Q η hQ i).hom =
        (ChainCohomology.homologyIso R Y P ε hP i).hom ≫
          IntegralComparison.Ext.SourceExactFunctorModule.component F R Y i (Opposite.op Z) ≫
            (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) i).map g.op := by
  let ιP := ChainResolutionOpposite.augmentation P ε
  let ιQ := ChainResolutionOpposite.augmentation Q η
  let : QuasiIso ιP := ChainResolutionOpposite.augmentation_quasiIso P ε
  let : QuasiIso ιQ := ChainResolutionOpposite.augmentation_quasiIso Q η
  let φ : (F.op.mapHomologicalComplex (.up ℕ)).obj P.op ⟶ Q.op :=
    (HomologicalComplex.opFunctor D (.down ℕ)).map β.op
  have hs : g.op ≫ ιQ.f 0 = F.op.map (ιP.f 0) ≫ φ.f 0 := by
    rw [ChainResolutionOpposite.augmentation_zero,
      ChainResolutionOpposite.augmentation_zero]
    exact (congrArg Quiver.Hom.op hβ).symm
  exact MixedResolutionCohomology.homology F R Y φ ιP ιQ g.op hs hP hQ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainMixedNaturality
