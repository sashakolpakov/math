import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution
import OAI.AlgebraicGeometry.Comparison.Betti.ComplexHypercohomologyForget
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ResolutionTotal

/-! # Bicomplex -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Bicomplex

noncomputable section

/-! The actual functorial Godement bicomplex and its original total augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0})

abbrev godementFunctor :=
  FunctorialResolution.resolutionFunctor (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)

instance godementFunctor_additive : (godementFunctor X).Additive := by
  exact @FunctorialResolution.resolutionFunctor_additive _ _ _ _ _ Functor.stalkFamilyFunctor_additive

def godementBicomplex (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ) :
    HomologicalComplex₂ (TopCat.Sheaf (ModuleCat.{0} ℂ) X) (.up ℕ) (.up ℕ) :=
  ((godementFunctor X).mapHomologicalComplex (.up ℕ)).obj K

variable {X} (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ)

def godementBicomplexAugmentation (q : ℕ) : K.X q ⟶ ((Bicomplex.godementBicomplex X K).X q).X 0 :=
  (Functor.stalkFamilyUnit X).app (K.X q)

theorem godementBicomplexAugmentation_comm (q q' : ℕ) :
    godementBicomplexAugmentation K q ≫ ((Bicomplex.godementBicomplex X K).d q q').f 0 =
      K.d q q' ≫ godementBicomplexAugmentation K q' :=
  ((Functor.stalkFamilyUnit X).naturality (K.d q q')).symm

theorem godementBicomplexAugmentation_comp_d (q : ℕ) :
    godementBicomplexAugmentation K q ≫ ((Bicomplex.godementBicomplex X K).X q).d 0 1 = 0 :=
  FunctorialResolution.resolution_augmentation_comp (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) (K.X q)

def godementTotal : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ℕ :=
  (Bicomplex.godementBicomplex X K).total (.up ℕ)

def godementTotalAugmentation : K ⟶ godementTotal K :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (godementBicomplex X K)) K
    (godementBicomplexAugmentation K) (fun q q' _ => godementBicomplexAugmentation_comm K q q')
    (godementBicomplexAugmentation_comp_d K)

theorem godementBicomplex_augmentation_exact (q : ℕ) :
    (ShortComplex.mk (godementBicomplexAugmentation K q)
      (((Bicomplex.godementBicomplex X K).X q).d 0 1) (godementBicomplexAugmentation_comp_d K q)).Exact :=
  Resolution.godement_augmentation_exact X (K.X q)

theorem godementBicomplex_augmentation_mono (q : ℕ) : Mono (godementBicomplexAugmentation K q) :=
  Functor.stalkFamilyUnit_mono (K.X q)

theorem godementBicomplex_exactAt_succ (q p : ℕ) :
    ((Bicomplex.godementBicomplex X K).X q).ExactAt (p + 1) :=
  Resolution.godementComplex_exactAt_succ X (K.X q) p

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Bicomplex
