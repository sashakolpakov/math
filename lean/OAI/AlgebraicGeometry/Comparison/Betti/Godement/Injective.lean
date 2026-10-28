import OAI.AlgebraicGeometry.Comparison.Betti.Godement.Resolution
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveFlasque
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso

/-! # Injective -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective

noncomputable section

/-! The actual Godement resolution computes the same global cohomology
as an injective resolution, through its augmentation-preserving comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X)

def godementResolutionData : ResolutionExactImage.Data F where
  complex := Resolution.godementComplex X F
  augmentation := (Functor.stalkFamilyUnit X).app F
  augmentation_d := FunctorialResolution.resolution_augmentation_comp
    (Functor.stalkFamilyFunctor X) (Functor.stalkFamilyUnit X) F
  isKernel := by
    have hbal : Balanced (TopCat.Sheaf (ModuleCat.{0} ℂ) X) :=
      inferInstanceAs (Balanced (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)))
    have : Mono ((Functor.stalkFamilyUnit X).app F) := Functor.stalkFamilyUnit_mono F
    exact (Resolution.godement_augmentation_exact X F).fIsKernel
  exact_succ := Resolution.godementComplex_exactAt_succ X F

def godementToInjective : Resolution.godementComplex X F ⟶ (injectiveResolution F).cocomplex :=
  ResolutionExactImage.toInjective (godementResolutionData F) (injectiveResolution F)

theorem godementToInjective_sections_quasiIso (U : Opens X) :
    QuasiIso (((FlasqueBiproduct.sections U).mapHomologicalComplex (.up ℕ)).map
      (godementToInjective F)) :=
  FlasqueNatQuasiIso.nat_sections_quasiIso (godementToInjective F)
    (Resolution.godementComplex_isFlasque X F)
    (fun n => InjectiveFlasque.injective_flasque ((injectiveResolution F).cocomplex.X n))
    (ResolutionExactImage.toInjective_quasiIso (godementResolutionData F) (injectiveResolution F)) U

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Injective
