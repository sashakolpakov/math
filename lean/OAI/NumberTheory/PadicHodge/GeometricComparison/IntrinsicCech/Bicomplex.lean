import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Instances
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation
import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge

/-! # Bicomplex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Bicomplex.IntrinsicCechBicomplex

noncomputable section

/-! The actual native Čech functor produces a bicomplex with exact augmented rows on every open cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Scheme.{0})
  {ι : Type} (U : ι → X.Opens)

abbrev Sheaves := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)

def bicomplex (K : CochainComplex (Sheaves R X) ℕ) :
    HomologicalComplex₂ (Sheaves R X) (.up ℕ) (.up ℕ) :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex (Functor.IntrinsicCechFunctor.sheafFunctor R X U) K

variable (K : CochainComplex (Sheaves R X) ℕ)

def augmentation (q : ℕ) : K.X q ⟶ ((bicomplex R X U K).X q).X 0 :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K q

theorem augmentation_comm (q q' : ℕ) :
    augmentation R X U K q ≫ ((bicomplex R X U K).d q q').f 0 =
      K.d q q' ≫ augmentation R X U K q' :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comm (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K q q'

theorem augmentation_comp_d (q : ℕ) :
    augmentation R X U K q ≫ ((bicomplex R X U K).X q).d 0 1 = 0 :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_comp_d (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K q

def edge :=
  @Functor.ResolutionTotal.FunctorResolutionTotal.edge (Sheaves R X) _ _ (Instances.IntrinsicCechInstances.hasCoproducts R X)
    (Functor.IntrinsicCechFunctor.sheafFunctor R X U) (Instances.IntrinsicCechInstances.additive R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K

theorem row_exact (hU : iSup U = ⊤) (q p : ℕ) :
    ((bicomplex R X U K).X q).ExactAt (p + 1) :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.row_exact (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K
    (Functor.IntrinsicCechFunctor.sheafAugmentation_quasiIso R X U hU) q p

theorem augmentation_exact_mono (hU : iSup U = ⊤) (q : ℕ) :
    (ShortComplex.mk (augmentation R X U K q) (((bicomplex R X U K).X q).d 0 1)
      (augmentation_comp_d R X U K q)).Exact ∧ Mono (augmentation R X U K q) :=
  Functor.ResolutionBicomplex.FunctorResolutionBicomplex.augmentation_exact_mono (Functor.IntrinsicCechFunctor.sheafFunctor R X U)
    (Functor.IntrinsicCechFunctor.sheafAugmentation R X U) K
    (Functor.IntrinsicCechFunctor.sheafAugmentation_quasiIso R X U hU) q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Bicomplex.IntrinsicCechBicomplex
