import OAI.AlgebraicGeometry.SheafCohomology.Cech.InjectiveComparison

/-! # Degree Zero -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.DegreeZero.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Global sections inject naturally into degree-zero native Čech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def cechGlobalSectionsToHZero (F : Sheaf AddCommGrpCat.{u} X) :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F ⟶
      ((cechComplexFunctor U).obj F.obj).homology 0 :=
  ((cechComplexFunctor U).obj F.obj).liftCycles
    (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U) 1 (by simp)
    (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d F U) ≫
      ((cechComplexFunctor U).obj F.obj).homologyπ 0

theorem cechGlobalSectionsToHZero_mono (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) : Mono (cechGlobalSectionsToHZero U F) := by
  let K := (cechComplexFunctor U).obj F.obj
  let f := K.liftCycles (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U) 1 (by simp)
    (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d F U)
  have hf : Mono (f ≫ K.iCycles 0) := by
    rw [show f ≫ K.iCycles 0 = GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U from
      K.liftCycles_i _ _ _ _]
    exact InjectiveComparison.TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U F hU
  let : Mono f := mono_of_mono f (K.iCycles 0)
  change Mono (f ≫ K.homologyπ 0)
  infer_instance

theorem cechGlobalSectionsToHZero_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    cechGlobalSectionsToHZero U F ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 0 =
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f ≫ cechGlobalSectionsToHZero U G := by
  let K := (cechComplexFunctor U).obj F.obj
  let L := (cechComplexFunctor U).obj G.obj
  let φ := (cechComplexFunctor U).map f.hom
  let a := GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U
  let b := GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation G U
  have h : K.liftCycles a 1 (by simp) (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d F U) ≫
      HomologicalComplex.cyclesMap φ 0 =
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f ≫
        L.liftCycles b 1 (by simp) (GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_comp_d G U) := by
    apply (cancel_mono (L.iCycles 0)).1
    dsimp only [K, L, φ]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    exact GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality F U f
  change (K.liftCycles a 1 (by simp) _ ≫ K.homologyπ 0) ≫
    HomologicalComplex.homologyMap φ 0 =
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map f ≫ (L.liftCycles b 1 (by simp) _ ≫ L.homologyπ 0)
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, h, Category.assoc]

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.DegreeZero.TopCat.Sheaf
