import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.GlobalAugmentationExactness

/-! # Degree Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZero

noncomputable section

/-! Global sections inject naturally into degree-zero native Čech cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

def cechGlobalSectionsToHZero (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).obj F ⟶
      ((cechComplexFunctor U).obj F.obj).homology 0 :=
  ((cechComplexFunctor U).obj F.obj).liftCycles
    (Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U) 1 (by simp)
    (Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F U) ≫
      ((cechComplexFunctor U).obj F.obj).homologyπ 0

theorem cechGlobalSectionsToHZero_mono (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) : Mono (cechGlobalSectionsToHZero U F) := by
  let K := (cechComplexFunctor U).obj F.obj
  let f := K.liftCycles (Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U) 1 (by simp)
    (Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F U)
  have hf : Mono (f ≫ K.iCycles 0) := by
    rw [show f ≫ K.iCycles 0 = Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U from
      K.liftCycles_i _ _ _ _]
    exact Cech.GlobalAugmentationExactness.IntrinsicCech.cechGlobalSectionsAugmentation_mono U F hU
  let : Mono f := mono_of_mono f (K.iCycles 0)
  change Mono (f ≫ K.homologyπ 0)
  infer_instance

theorem cechGlobalSectionsToHZero_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G) :
    cechGlobalSectionsToHZero U F ≫
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 0 =
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map f ≫ cechGlobalSectionsToHZero U G := by
  let K := (cechComplexFunctor U).obj F.obj
  let L := (cechComplexFunctor U).obj G.obj
  let φ := (cechComplexFunctor U).map f.hom
  let a := Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation F U
  let b := Cech.GlobalAugmentation.IntrinsicCech.cechGlobalSectionsAugmentation G U
  have h : K.liftCycles a 1 (by simp) (Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d F U) ≫
      HomologicalComplex.cyclesMap φ 0 =
      (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map f ≫
        L.liftCycles b 1 (by simp) (Cech.GlobalAugmentationComplex.IntrinsicCech.cechGlobalSectionsAugmentation_comp_d G U) := by
    apply (cancel_mono (L.iCycles 0)).1
    dsimp only [K, L, φ]
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    exact Cech.GlobalAugmentationNaturality.IntrinsicCech.cechGlobalSectionsAugmentation_naturality F U f
  change (K.liftCycles a 1 (by simp) _ ≫ K.homologyπ 0) ≫
    HomologicalComplex.homologyMap φ 0 =
      (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).map f ≫ (L.liftCycles b 1 (by simp) _ ≫ L.homologyπ 0)
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, h, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.DegreeZero
