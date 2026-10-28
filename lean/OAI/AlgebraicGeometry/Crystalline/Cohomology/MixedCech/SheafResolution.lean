import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Resolution

/-! # Sheaf Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafResolution.MixedCechSheafResolution

noncomputable section

/-! # The Čech resolution starts from the actual coefficient sheaf -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u v

variable (R : Type v) [CommRing R] (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R))

def sourceIso :
    ((Presheaf.MixedCechPresheaf.sheafification R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ (Presheaf.MixedCechPresheaf.Presheaves R X)).obj F.obj) ≅
        (CochainComplex.single₀
          (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R))).obj F :=
  (HomologicalComplex.singleMapHomologicalComplex (Presheaf.MixedCechPresheaf.sheafification R X)
    (ComplexShape.up ℕ) 0).app F.obj ≪≫
      (CochainComplex.single₀ _).mapIso (sheafificationIso F).symm

def augmentation :
    (CochainComplex.single₀
      (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R))).obj F ⟶
        Presheaf.MixedCechPresheaf.sheafComplex R X U F.obj :=
  (sourceIso R X F).inv ≫ Presheaf.MixedCechPresheaf.sheafAugmentation R X U F.obj

theorem quasiIso (hU : iSup U = ⊤) : QuasiIso (augmentation R X U F) := by
  have : QuasiIso (Presheaf.MixedCechPresheaf.sheafAugmentation R X U F.obj) :=
    Resolution.MixedCechResolution.augmentation_quasiIso R X U F.obj hU
  exact quasiIso_comp _ _

def degreeZeroIso (hU : iSup U = ⊤) :
    (Presheaf.MixedCechPresheaf.sheafComplex R X U F.obj).homology 0 ≅ F :=
  Resolution.MixedCechResolution.degreeZeroHomologyIso R X U F.obj hU ≪≫ (sheafificationIso F).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.SheafResolution.MixedCechSheafResolution
