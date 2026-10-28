import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.SheafDegreeZero
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso

/-! # Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.DegreeZero.CechDegreeZero

noncomputable section

/-! The actual direct Čech complex identifies global sections of a module sheaf with its zero-cocycles through the canonical augmentation. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (F : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R))
  {ι : Type u} (U : ι → X.left.Opens) (hU : iSup U = ⊤)

include hU in
theorem augmentation_quasiIsoAt_zero : QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U F.obj) 0 := by
  have ha : QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.augmentation R X.left U F.obj ⊤) 0 :=
    SheafDegreeZero.CechSheafDegreeZero.augmentation_quasiIsoAt_zero R X.left F U hU ⊤
  have : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R X F.obj).inv :=
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R X F.obj).isIso_inv
  have : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom :=
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).isIso_hom
  have hs : QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R X F.obj).inv 0 :=
    quasiIsoAt_of_isIso _ 0
  have ht : QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom 0 :=
    quasiIsoAt_of_isIso _ 0
  have hm : QuasiIsoAt (AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.augmentation R X.left U F.obj ⊤ ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom) 0 :=
    quasiIsoAt_comp _ _ 0 (hφ := ha) (hφ' := ht)
  have h : QuasiIsoAt ((AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.sourceIso R X F.obj).inv ≫
      AlgebraicGeometry.Crystalline.Cohomology.Cech.AugmentedSections.CechAugmentedSections.augmentation R X.left U F.obj ⊤ ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.complexIso R X U F.obj).hom) 0 :=
    quasiIsoAt_comp _ _ 0 (hφ := hs) (hφ' := hm)
  exact (AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionsIso.CechGlobalSectionsIso.augmentation_comp R X U F.obj) ▸ h

def initial : ShortComplex (ModuleCat.{u} R) :=
  AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.initialShort (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U F.obj)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 (F.obj.obj (op ⊤)) 0 1)

include hU in
theorem initial_leftExact : (initial R X F U).Exact ∧ Mono (initial R X F U).f :=
  (AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion.quasiIsoAt_zero_iff (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U F.obj)
    (HomologicalComplex.single_obj_d (ComplexShape.up ℕ) 0 (F.obj.obj (op ⊤)) 0 1)).mp
      (augmentation_quasiIsoAt_zero R X F U hU)

include hU in
theorem exists_augmentation (z : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj F.obj).X 0)
    (hz : ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).obj F.obj).d 0 1 z = 0) :
    ∃ x : F.obj.obj (op ⊤), (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U F.obj).f 0 x = z :=
  (ShortComplex.moduleCat_exact_iff (initial R X F U)).mp (initial_leftExact R X F U hU).1 z hz

include hU in
theorem augmentation_injective : Function.Injective ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation R X U F.obj).f 0) :=
  (ModuleCat.mono_iff_injective (initial R X F U).f).mp (initial_leftExact R X F U hU).2

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.DegreeZero.CechDegreeZero
