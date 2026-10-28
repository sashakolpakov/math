import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorBaseChange

/-! # Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionBaseChange

noncomputable section

/-! Products of sections commute with arbitrary pullback under the canonical tensor comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem tensorPullbackComparison_unit_inverse (f : X ⟶ Y) :
    (Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule Y)).inv ≫
      PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) =
      (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).inv ≫
        Bifunctor.tensorModuleMap (Line.Bundles.structureModulePullbackIso f).inv (Line.Bundles.structureModulePullbackIso f).inv := by
  let u : (Scheme.Modules.pullback f).obj
      (ProductSheaf.tensorModule (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y)) ≅ Line.Bundles.structureModule X :=
    (Scheme.Modules.pullback f).mapIso (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule Y)) ≪≫
      Line.Bundles.structureModulePullbackIso f
  let v : ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y))
      ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y)) ≅ Line.Bundles.structureModule X :=
    Bifunctor.tensorModuleMapIso (Line.Bundles.structureModulePullbackIso f) (Line.Bundles.structureModulePullbackIso f) ≪≫
      ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)
  have h : PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) ≫ v.hom = u.hom :=
    PullbackUnits.tensorPullbackComparison_unit_formula f
  have hi : u.inv ≫ PullbackComparison.tensorPullbackComparison f (Line.Bundles.structureModule Y) (Line.Bundles.structureModule Y) = v.inv := by
    apply (cancel_mono v.hom).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => u.inv ≫ a) h).trans
        (u.inv_hom_id.trans v.inv_hom_id.symm))
  exact (Category.assoc _ _ _).symm.trans hi

theorem tensorPullbackComparison_section (f : X ⟶ Y) {L M : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ L) (t : Line.Bundles.structureModule Y ⟶ M) :
    Ample.LineBundles.pullbackSection f (ProductSections.tensorProductSection s t) ≫ PullbackComparison.tensorPullbackComparison f L M =
      ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) := by
  change ((Line.Bundles.structureModulePullbackIso f).inv ≫
    (Scheme.Modules.pullback f).map
      ((ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule Y)).inv ≫ Bifunctor.tensorModuleMap s t)) ≫
      PullbackComparison.tensorPullbackComparison f L M =
    (ProductSheaf.tensorModuleUnitLeftIso (Line.Bundles.structureModule X)).inv ≫
      Bifunctor.tensorModuleMap ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s)
        ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map t)
  rw [Functor.map_comp, ← Bifunctor.tensorModuleMap_comp]
  simp only [Category.assoc]
  rw [PullbackComparison.tensorPullbackComparison_natural]
  exact (congrArg (fun a => a ≫ Bifunctor.tensorModuleMap
    ((Scheme.Modules.pullback f).map s) ((Scheme.Modules.pullback f).map t))
      (tensorPullbackComparison_unit_inverse f)).trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionBaseChange
