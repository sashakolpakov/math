import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Bicomplex
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Injective Row -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.InjectiveRow

noncomputable section

/-! The source augmentation into the actual Hom complex is a
quasi-isomorphism for injective coefficient objects. No projectivity of
the source resolution terms is required. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (P : ChainComplex C ℕ)
  {Z : C} (ε : P ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] (Y : C)

def augmentation : (CochainComplex.single₀ _).obj (ModuleCat.of R (Abelian.Ext.{z} Z Y 0)) ⟶
    Acyclic.ChainCohomology.complex R Y P :=
  Contravariant.ResolutionZero.augmentation R Y P.op (ChainResolutionOpposite.augmentation P ε)

omit [QuasiIso ε] in
theorem augmentation_zero : (augmentation R P ε Y).f 0 =
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).map (ε.f 0).op := by
  exact (Contravariant.ResolutionZero.augmentation_zero R Y P.op
    (ChainResolutionOpposite.augmentation P ε)).trans
      (congrArg (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).map
        (ChainResolutionOpposite.augmentation_zero P ε))

variable [Injective Y]

include ε in
theorem positive_isZero (n : ℕ) : IsZero ((Acyclic.ChainCohomology.complex R Y P).homology (n + 1)) := by
  let : Subsingleton (Abelian.Ext.{z} Z Y (n + 1)) := Abelian.Ext.subsingleton_of_injective Z Y n
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (Acyclic.ChainCohomology.homologyIso R Y P ε
      (fun a q => Abelian.Ext.subsingleton_of_injective (P.X a) Y q) (n + 1))

theorem augmentation_quasiIso : QuasiIso (augmentation R P ε Y) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
      exact Contravariant.ResolutionZero.augmentation_quasiIsoAt_zero R Y P.op
        (ChainResolutionOpposite.augmentation P ε)
  | succ n =>
      apply (quasiIsoAt_iff_exactAt _ (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)).mpr
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr (positive_isZero R P ε Y n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.InjectiveRow
