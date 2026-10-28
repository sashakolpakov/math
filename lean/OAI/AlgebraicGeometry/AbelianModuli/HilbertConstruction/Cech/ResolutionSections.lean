import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.InjectiveBicomplex

/-! # Resolution Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionSections.IntrinsicCech

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X)

/-- Global sections applied degreewise to the chosen injective resolution. -/
noncomputable def cechResolutionSectionsComplex
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution F).cocomplex

noncomputable def cechResolutionSectionsMap
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (phi : (injectiveResolution F).cocomplex ⟶
      (injectiveResolution G).cocomplex) :
    cechResolutionSectionsComplex F ⟶
      cechResolutionSectionsComplex G :=
  ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map phi

@[simp]
theorem cechResolutionSectionsMap_f
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (phi : (injectiveResolution F).cocomplex ⟶
      (injectiveResolution G).cocomplex) (q : ℕ) :
    (cechResolutionSectionsMap phi).f q =
      (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (phi.f q) :=
  rfl

/-- The row augmentation from global sections of the resolution to native
Cech degree zero. -/
noncomputable def cechResolutionHorizontalAugmentation
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    (cechResolutionSectionsComplex F).X q ⟶
      ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).X q).X 0 :=
  GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation
    ((injectiveResolution F).cocomplex.X q) U

@[simp]
theorem cechResolutionHorizontalAugmentation_eq
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    cechResolutionHorizontalAugmentation U F q =
      GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation
        ((injectiveResolution F).cocomplex.X q) U :=
  rfl

theorem cechResolutionHorizontalAugmentation_comm
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q q' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel q q') :
    cechResolutionHorizontalAugmentation U F q ≫
        ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).d q q').f 0 =
      (cechResolutionSectionsComplex F).d q q' ≫
        cechResolutionHorizontalAugmentation U F q' := by
  let I := injectiveResolution F
  change GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
      ((cechComplexFunctor U).map (I.cocomplex.d q q').hom).f 0 =
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map (I.cocomplex.d q q') ≫
      GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation (I.cocomplex.X q') U
  exact GlobalAugmentationNaturality.IntrinsicCech.cechGlobalSectionsAugmentation_naturality
    (U := U) (F := I.cocomplex.X q) (I.cocomplex.d q q')

theorem cechResolutionHorizontalAugmentation_comp_d
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    cechResolutionHorizontalAugmentation U F q ≫
      ((InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).X q).d 0 1 = 0 := by
  let I := injectiveResolution F
  change GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
    ((cechComplexFunctor U).obj (I.cocomplex.X q).obj).d 0 1 = 0
  exact GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d (I.cocomplex.X q) U

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionSections.IntrinsicCech
