import OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechCoordinates

/-! # Global Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.GlobalCoordinates

noncomputable section

/-! The native Cech augmentation is actual restriction of a global section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)
  (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem abelianCechGlobalAugmentation_coordinates
    (x : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F) (a : Fin 1 → I) :
    Abelian.CechCoordinates.abelianCechCoordinates F.obj U 0 (SheafCohomology.Cech.GlobalSections.TopCat.Sheaf.cechGlobalSectionsAugmentation F U x) a =
      F.obj.map (homOfLE (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ ⊤ from le_top)).op
        ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).hom.app F x) := by
  let e := CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  let t := e.hom.app (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTerm F U 0)
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation F U) x)
  let y := (AddEquiv.piCongrRight fun b : Fin 1 → I =>
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun j : Fin 1 => U (b j)))))).addCommGroupIsoToAddEquiv)
    (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U 0 (⊤ : Opens X) t)
  have ht : t = (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation F U).hom.app (op ⊤) (e.hom.app F x) :=
    ConcreteCategory.congr_hom (e.hom.naturality (SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation F U)) x
  rw [Abelian.CechCoordinates.abelianCechCoordinates_apply]
  change (Abelian.CechCoordinates.abelianCechIntersectionIso F.obj U a).hom
    (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0 ((SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U 0).symm y) a) = _
  rw [AddEquiv.apply_symm_apply]
  change (Abelian.CechCoordinates.abelianCechIntersectionIso F.obj U a).hom
    ((F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun j : Fin 1 => U (a j)))))).hom
        (SheafCohomology.Cech.Terms.TopCat.Sheaf.cechTermSectionsAddEquiv F U 0 (⊤ : Opens X) t a)) = _
  rw [ht, SheafCohomology.Cech.Augmentation.TopCat.Sheaf.cechAugmentation_apply]
  change (F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _) (e.hom.app F x) =
    F.obj.map _ (e.hom.app F x)
  apply ConcreteCategory.congr_hom
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.GlobalCoordinates
