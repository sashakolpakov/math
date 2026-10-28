import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Unit Left Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitLeftNaturality

noncomputable section

/-! The actual structure-module tensor unit is natural in the arbitrary module factor, including its inverse. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}} {M N : X.Modules}

theorem unitLeftBilinear_natural (f : M ⟶ N) :
    (PullbackUnits.unitLeftBilinear N).precomp (𝟙 (Line.Bundles.structureModule X)) f =
      (PullbackUnits.unitLeftBilinear M).postcomp f := by
  apply Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply DFunLike.ext
  intro r
  apply DFunLike.ext
  intro m
  exact ((Powers.SheafMultilinearMap.homApp f U).map_smul r m).symm

theorem tensorModuleUnitLeftIso_hom_natural (f : M ⟶ N) :
    Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) f ≫ (ProductSheaf.tensorModuleUnitLeftIso N).hom =
      (ProductSheaf.tensorModuleUnitLeftIso M).hom ≫ f := by
  apply (Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv (Line.Bundles.structureModule X) M N).injective
  rw [← Bifunctor.tensorBilinear_postcomp, Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, Bifunctor.tensorModuleMap_spec,
    ← Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp, Bifunctor.tensorBilinear_postcomp,
    PullbackUnits.tensorModuleUnitLeftIso_formula, Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp,
    PullbackUnits.tensorModuleUnitLeftIso_formula]
  exact unitLeftBilinear_natural f

theorem tensorModuleUnitLeftIso_inv_natural (f : M ⟶ N) :
    f ≫ (ProductSheaf.tensorModuleUnitLeftIso N).inv =
      (ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) f := by
  apply (cancel_mono (ProductSheaf.tensorModuleUnitLeftIso N).hom).mp
  calc
    (f ≫ (ProductSheaf.tensorModuleUnitLeftIso N).inv) ≫ (ProductSheaf.tensorModuleUnitLeftIso N).hom = f := by simp
    _ = ((ProductSheaf.tensorModuleUnitLeftIso M).inv ≫ Bifunctor.tensorModuleMap (𝟙 (Line.Bundles.structureModule X)) f) ≫
        (ProductSheaf.tensorModuleUnitLeftIso N).hom := by
      rw [Category.assoc, tensorModuleUnitLeftIso_hom_natural]
      simp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitLeftNaturality
