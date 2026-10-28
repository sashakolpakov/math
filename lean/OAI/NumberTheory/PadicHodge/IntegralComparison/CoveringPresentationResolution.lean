import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresheafQuasiIso

/-! # Covering Presentation Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution

noncomputable section

/-! Actual tuples of maps to covering objects resolve the original constant coefficient sheaf. -/

open _root_.CategoryTheory

universe u v

variable {C : Type (max u v)} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] {ι : Type v} (F : ι → C)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ J U)

def complex : ChainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafComplex R (CoveringPresentationPresheaf.presentations F) J

def augmentation : complex J R F ⟶
    (ChainComplex.single₀ (Sheaf J (ModuleCat.{max u v} R))).obj
      ((constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.sheafAugmentation R (CoveringPresentationPresheaf.presentations F) J

include hcover in
theorem augmentation_quasiIso : QuasiIso (augmentation J R F) := by
  let a := AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R (CoveringPresentationPresheaf.presentations F)
  let S := (presheafToSheaf J (ModuleCat.{max u v} R)).mapHomologicalComplex (.down ℕ)
  let h : QuasiIso (S.map a) :=
    CoveringPresheafQuasiIso.quasiIso J R a F hcover
      (CoveringPresentationPresheaf.restricted_augmentation F R)
  let e := (HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J (ModuleCat.{max u v} R))
    (.down ℕ) 0).app (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.coefficientPresheaf (C := C) R)
  let : IsIso e.hom := e.isIso_hom
  let he : QuasiIso e.hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h) (hφ' := he)

def degreeZeroIso : (complex J R F).homology 0 ≅
    ((constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)) := by
  let h : QuasiIso (augmentation J R F) := augmentation_quasiIso J R F hcover
  let : QuasiIsoAt (augmentation J R F) 0 := h.quasiIsoAt 0
  exact isoOfQuasiIsoAt (augmentation J R F) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.down ℕ) 0
      ((constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution
