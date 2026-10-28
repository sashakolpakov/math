import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison

/-! # Cech Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechComparison

noncomputable section

/-!
The map from actual abelian Cech cohomology to sheaf Ext cohomology for any
open cover. Only the horizontal edge is inverted; no acyclicity of cover
intersections is required. The construction is natural in the coefficient sheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

local instance abelianCechSections_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def abelianCechToDerived (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology (n + 1) ⟶
      ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).obj (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F) :=
  HomologicalComplex.homologyMap (SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1) ≫
    (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫
      ((injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)).isoRightDerivedObj
        (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv

def abelianCechToSheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology (n + 1) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F :=
  abelianCechToDerived U F hU n ≫
    (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F (n + 1)).symm.toAddCommGrpIso.hom

theorem abelianCechToDerived_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f.hom) (n + 1) ≫
        abelianCechToDerived U G hU n =
      abelianCechToDerived U F hU n ≫
        ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
  let IF := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let IG := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf G)
  let phi : InjectiveResolution.Hom IF IG f :=
    { hom := InjectiveResolution.desc f IG IF
      ι_f_zero_comp_hom_f_zero := InjectiveResolution.desc_commutes_zero f IG IF }
  let t := SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionTotalMap U phi.hom
  let s := SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf.cechResolutionSectionsMap phi.hom
  have hv :
      HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f.hom) (n + 1) ≫
          HomologicalComplex.homologyMap (SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U G) (n + 1) =
        HomologicalComplex.homologyMap (SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1) ≫
          HomologicalComplex.homologyMap t (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
      (SheafCohomology.Cech.InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge_naturality U f phi).symm
  have hh : HomologicalComplex.homologyMap s (n + 1) ≫
        (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).hom =
      (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).hom ≫
        HomologicalComplex.homologyMap t (n + 1) := by
    change HomologicalComplex.homologyMap s (n + 1) ≫
        HomologicalComplex.homologyMap (SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U G) (n + 1) =
      HomologicalComplex.homologyMap (SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F) (n + 1) ≫
        HomologicalComplex.homologyMap t (n + 1)
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
      (SheafCohomology.Cech.HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge_naturality U f phi)
  have hi : HomologicalComplex.homologyMap t (n + 1) ≫
        (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).inv =
      (SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫
        HomologicalComplex.homologyMap s (n + 1) := by
    rw [(SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).comp_inv_eq, Category.assoc, hh]
    simp
  have hd : HomologicalComplex.homologyMap s (n + 1) ≫
        (IG.isoRightDerivedObj (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv =
      (IF.isoRightDerivedObj (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv ≫
        ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
    exact (@InjectiveResolution.isoRightDerivedObj_inv_naturality
      _ _ _ _ _ _ _ _ _ f IF IG phi.hom phi.ι_f_zero_comp_hom_f_zero
      (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (abelianCechSections_additive (X := X)) (n + 1)).symm
  unfold abelianCechToDerived
  rw [← Category.assoc, ← Category.assoc, hv, Category.assoc, Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap t (n + 1)), hi,
    Category.assoc, hd]
  simp only [Category.assoc]
  rfl

theorem abelianCechToSheaf_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map f.hom) (n + 1) ≫
        abelianCechToSheaf U G hU n =
      abelianCechToSheaf U F hU n ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map f := by
  unfold abelianCechToSheaf
  rw [← Category.assoc, abelianCechToDerived_naturality]
  simp only [Category.assoc]
  congr 1
  ext x
  exact SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections_symm_naturality f (n + 1) x

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechComparison
