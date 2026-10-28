import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.ChainResolutionOppositeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainCohomology

/-! # Chain Functor Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality

noncomputable section

/-! Actual source-resolution cochain maps compute the original exact-functor and source maps on Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (P : ChainComplex C ℕ) (Q : ChainComplex D ℕ)
  (β : Q ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P)

def map : ChainCohomology.complex R Y P ⟶ ChainCohomology.complex R (F.obj Y) Q :=
  Contravariant.ExactFunctorComplex.map F R Y P.op ≫
    ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0).mapHomologicalComplex (.up ℕ)).map
      ((HomologicalComplex.opFunctor D (.down ℕ)).map β.op)

variable {Z : C} {W : D} (ε : P ⟶ (ChainComplex.single₀ C).obj Z)
  (η : Q ⟶ (ChainComplex.single₀ D).obj W) [QuasiIso ε] [QuasiIso η]
  (g : W ⟶ F.obj Z) (hβ : β.f 0 ≫ F.map (ε.f 0) = η.f 0 ≫ g)
  (hP : ∀ a q, Subsingleton (Ext.{z} (P.X a) Y (q + 1)))
  (hQ : ∀ a q, Subsingleton (Ext.{z} (Q.X a) (F.obj Y) (q + 1)))
  (hFP : ∀ a q, Subsingleton (Ext.{z} (F.obj (P.X a)) (F.obj Y) (q + 1)))

include hβ hFP in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap (ChainFunctorNaturality.map F R Y P Q β) i ≫
    (ChainCohomology.homologyIso R (F.obj Y) Q η hQ i).hom =
      (ChainCohomology.homologyIso R Y P ε hP i).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component F R Y i (Opposite.op Z) ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) i).map g.op := by
  let FP := (F.mapHomologicalComplex (.down ℕ)).obj P
  let κ := ChainResolutionExactFunctor.augmentation F P ε
  let hκq : QuasiIso κ := ChainResolutionExactFunctor.augmentation_quasiIso F P ε
  let ιP := ChainResolutionOpposite.augmentation P ε
  let ιQ := ChainResolutionOpposite.augmentation Q η
  let ιFP : (CochainComplex.single₀ Dᵒᵖ).obj (F.op.obj (Opposite.op Z)) ⟶
      (F.op.mapHomologicalComplex (.up ℕ)).obj P.op := ChainResolutionOpposite.augmentation FP κ
  let hιFP : QuasiIso ιFP := ChainResolutionOpposite.augmentation_quasiIso FP κ
  let φ := (HomologicalComplex.opFunctor D (.down ℕ)).map β.op
  let c := Contravariant.ExactFunctorComplex.map F R Y P.op
  let d := ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0).mapHomologicalComplex (.up ℕ)).map φ
  have hκ : β.f 0 ≫ κ.f 0 = η.f 0 ≫ g :=
    (congrArg (fun a => β.f 0 ≫ a) (ChainResolutionExactFunctor.augmentation_zero F P ε)).trans hβ
  have hn := Contravariant.ResolutionNaturality.homology R (F.obj Y) ιFP ιQ hFP hQ φ g.op
    (ChainResolutionOppositeNaturality.augmentation FP Q κ η β g hκ) i
  have hf := Contravariant.ExactFunctorCohomology.homology F R Y P.op ιP ιFP
    (ChainResolutionExactFunctor.opposite_augmentation_zero F P ε) hP hFP i
  exact (congrArg (fun a => a ≫ (ChainCohomology.homologyIso R (F.obj Y) Q η hQ i).hom)
    (HomologicalComplex.homologyMap_comp c d i)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => HomologicalComplex.homologyMap c i ≫ a) hn).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun a => a ≫ (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) i).map g.op) hf).trans
              (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ChainFunctorNaturality
