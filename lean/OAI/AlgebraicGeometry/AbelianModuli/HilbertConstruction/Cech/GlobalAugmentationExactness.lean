/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafCechInjectiveComparison.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FlasqueIntrinsicCechExactness

/-! # Global Augmentation Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationExactness.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X)

/-- The native Cech short complex augmented by global sections. -/
noncomputable def cechGlobalSectionsNativeShortComplex
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U)
    (((cechComplexFunctor U).obj F.obj).d 0 1)
    (GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F U)

noncomputable def cechGlobalSectionsMappedAugmentedShortComplex
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U))
    ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U 0))
    (by
      have hzero := SheafAugmentation.IntrinsicCech.cechAugmentation_comp F U
      calc
        _ = (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map
            (SheafAugmentation.IntrinsicCech.cechAugmentation F U ≫ SheafDifferential.IntrinsicCech.cechDifferential F U 0) :=
          ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map_comp _ _).symm
        _ = (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map 0 :=
          congrArg (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map hzero
        _ = 0 := (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map_zero _ _)

theorem cechGlobalSections_map_augmented_exact_and_mono
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hU : ⨆ i, U i = ⊤) :
    (cechGlobalSectionsMappedAugmentedShortComplex U F).Exact ∧
      Mono ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U)) := by
  let S := SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U
  have hS : S.Exact := ZeroCycleStalks.IntrinsicCech.cechAugmentedShortComplex_exact F U hU
  have hmono : Mono S.f := by
    change Mono (SheafAugmentation.IntrinsicCech.cechAugmentation F U)
    exact SheafResolution.IntrinsicCech.cechAugmentation_mono F U hU
  have hmap := (((Functor.preservesFiniteLimits_tfae
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X)).out 4 2 rfl rfl).mp
      (inferInstance : PreservesFiniteLimits (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X)))
        S ⟨hS, hmono⟩
  refine ⟨?_, by simpa [S, SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex] using hmap.2⟩
  have hex := (ShortComplex.ab_exact_iff _).mp hmap.1
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact hex x hx

/-- The native Cech short complex augmented by global sections is exact for an
open cover. -/
theorem cechGlobalSectionsNativeShortComplex_exact
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hU : ⨆ i, U i = ⊤) :
    (cechGlobalSectionsNativeShortComplex U F).Exact := by
  let S := SheafAugmentation.IntrinsicCech.cechAugmentedShortComplex F U
  have hmap := cechGlobalSections_map_augmented_exact_and_mono U F hU
  have hcomm := (GlobalSectionsComplex.IntrinsicCech.cechGlobalSectionsComplexIso F U).hom.comm 0 1
  change (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0).hom ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 =
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) ≫
      (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 1).hom at hcomm
  let e : cechGlobalSectionsMappedAugmentedShortComplex U F ≅
      cechGlobalSectionsNativeShortComplex U F :=
    ShortComplex.isoMk (Iso.refl _)
      (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0)
      (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 1)
      (by
        change 𝟙 _ ≫ ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map
            (SheafAugmentation.IntrinsicCech.cechAugmentation F U) ≫
              (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0).hom) =
          (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) ≫
            (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0).hom
        rw [Category.id_comp]) hcomm
  exact ShortComplex.exact_of_iso e hmap.1

/-- The native Cech augmentation on global sections is monic for an open cover. -/
theorem cechGlobalSectionsAugmentation_mono
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hU : ⨆ i, U i = ⊤) :
    Mono (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U) := by
  have hmap := cechGlobalSections_map_augmented_exact_and_mono U F hU
  let : Mono ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map
      (SheafAugmentation.IntrinsicCech.cechAugmentation F U)) := hmap.2
  change Mono ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (SheafAugmentation.IntrinsicCech.cechAugmentation F U) ≫
    (GlobalAugmentation.IntrinsicCech.cechGlobalSectionsXIso F U 0).hom)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationExactness.IntrinsicCech
