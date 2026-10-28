import OAI.AlgebraicGeometry.Comparison.Betti.FunctorialResolution
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Locality

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution

noncomputable section

/-! The actual additive Godement resolution, with flasque terms and
neighborhood support preservation in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.FunctorialResolution

variable (X : TopCat.{0})

abbrev godementResidual (n : ℕ) := FunctorialResolution.residualFunctor (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) n

abbrev godementTerm (n : ℕ) := FunctorialResolution.resolutionTerm (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) n

abbrev godementComplex (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
  FunctorialResolution.resolutionComplex (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) F

theorem godementComplex_isFlasque (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((godementComplex X F).X n) :=
  Functor.stalkFamilyFunctor_isFlasque ((godementResidual X n).obj F)

theorem godementComplex_exactAt_succ (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) (n : ℕ) :
    (godementComplex X F).ExactAt (n + 1) :=
  FunctorialResolution.resolutionComplex_exactAt_succ (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)
    Functor.stalkFamilyUnit_mono F n

theorem godement_augmentation_exact (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) :
    (ShortComplex.mk ((Functor.stalkFamilyUnit X).app F) ((godementComplex X F).d 0 1)
      (FunctorialResolution.resolution_augmentation_comp (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) F)).Exact :=
  FunctorialResolution.resolution_augmentation_exact (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X)
    Functor.stalkFamilyUnit_mono F

variable {X} {F G : TopCat.Sheaf (ModuleCat.{0} ℂ) X}

theorem godementResidualMap_vanishesOn (f : F ⟶ G) (U : Opens X)
    (hf : Locality.VanishesOn f U) (n : ℕ) : Locality.VanishesOn ((godementResidual X n).map f) U := by
  induction n with
  | zero => exact hf
  | succ n ih => exact Locality.quotientMap_vanishesOn ((godementResidual X n).map f) U ih

theorem godementTermMap_vanishesOn (f : F ⟶ G) (U : Opens X)
    (hf : Locality.VanishesOn f U) (n : ℕ) : Locality.VanishesOn ((godementTerm X n).map f) U :=
  Locality.stalkFamilyMap_vanishesOn ((godementResidual X n).map f) U
    (godementResidualMap_vanishesOn f U hf n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution
