import OAI.NumberTheory.PadicHodge.GeometricComparison.AugmentedInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

/-! # Exact Injective -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective.ExactInjectivePullback

noncomputable section

/-! An exact functor gives a canonical augmented comparison from a
transported injective resolution to a chosen target injective resolution. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  {Z : C} {Z' : D} (e : F.obj Z ≅ Z')
  (I : InjectiveResolution Z) (I' : InjectiveResolution Z')

def source : CochainComplex D ℕ := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex

def augmentation : (CochainComplex.single₀ D).obj Z' ⟶ source F I :=
  IntegralComparison.Single.ComplexTransport.map F e I.ι

def map : source F I ⟶ I'.cocomplex :=
  AugmentedInjective.AugmentedInjectiveComparison.map (source F I) (augmentation F e I)
    (IntegralComparison.Single.ComplexTransportNaturality.quasiIso F e I.ι) I'

theorem augmentation_map : augmentation F e I ≫ map F e I I' = I'.ι :=
  AugmentedInjective.AugmentedInjectiveComparison.augmentation (source F I) (augmentation F e I)
    (IntegralComparison.Single.ComplexTransportNaturality.quasiIso F e I.ι) I'

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExactInjective.ExactInjectivePullback
