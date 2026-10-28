import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison

/-! # Comparison Naturality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.ComparisonNaturality.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

noncomputable local instance e35NaturalitySections_additive :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

private theorem cechPositiveVerticalHomologyIso_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    (Comparison.TopCat.Sheaf.cechPositiveVerticalHomologyIso U F hH n).hom =
      HomologicalComplex.homologyMap (InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1) := rfl

private theorem cechPositiveHorizontalHomologyIso_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).hom =
      HomologicalComplex.homologyMap (HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F) (n + 1) := rfl

private theorem cechPositiveRightDerivedIso_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    (Comparison.TopCat.Sheaf.cechPositiveRightDerivedIso U F hU hH n).hom =
      (Comparison.TopCat.Sheaf.cechPositiveVerticalHomologyIso U F hH n).hom ≫ ((Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫ ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv) := rfl

private theorem cechHomologySuccIsoOfAcyclicIntersections_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    (Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U F hU hH n).hom =
      (Comparison.TopCat.Sheaf.cechPositiveRightDerivedIso U F hU hH n).hom ≫ (Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F (n + 1)).symm.toAddCommGrpIso.hom := rfl

private theorem positiveIsoSquare_inv_naturality
    {A B C D : AddCommGrpCat.{u}} (e : A ≅ B) (e' : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  rw [e'.comp_inv_eq, Category.assoc, h]
  simp

private theorem cechPositiveDerived_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F))
      (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)) f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (HorizontalComparison.TopCat.Sheaf.cechResolutionSectionsMap phi.hom) (n + 1) ≫
      ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)).isoRightDerivedObj
        (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv =
    ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).isoRightDerivedObj
        (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv ≫
      ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
  let hGlobalSectionsAdditive : (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
    (CategoryTheory.constantSheafΓAdj
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive
  have h := @InjectiveResolution.isoRightDerivedObj_inv_naturality
    _ _ _ _ _ _ _ _ _ f
    (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F))
    (injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)) phi.hom
    phi.ι_f_zero_comp_hom_f_zero (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X)
    hGlobalSectionsAdditive (n + 1)
  exact h.symm

private theorem cechPositiveRightDerivedIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤)
    (hF : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F)
    (hG : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.hom) (n + 1) ≫
      (Comparison.TopCat.Sheaf.cechPositiveRightDerivedIso U G hU hG n).hom =
    (Comparison.TopCat.Sheaf.cechPositiveRightDerivedIso U F hU hF n).hom ≫
      ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
  let IF := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)
  let IG := injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf G)
  let phi : InjectiveResolution.Hom IF IG f :=
    { hom := InjectiveResolution.desc f IG IF
      ι_f_zero_comp_hom_f_zero := by
        change IF.ι.f 0 ≫ (InjectiveResolution.desc f IG IF).f 0 =
          f ≫ IG.ι.f 0
        exact InjectiveResolution.desc_commutes_zero f IG IF }
  let verticalF := InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F
  let verticalG := InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U G
  let horizontalF := HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F
  let horizontalG := HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U G
  let totalMap := InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionTotalMap U phi.hom
  let sectionsMap := HorizontalComparison.TopCat.Sheaf.cechResolutionSectionsMap phi.hom
  have hvertical :
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) ≫
          (Comparison.TopCat.Sheaf.cechPositiveVerticalHomologyIso U G hG n).hom =
        (Comparison.TopCat.Sheaf.cechPositiveVerticalHomologyIso U F hF n).hom ≫
          HomologicalComplex.homologyMap totalMap (n + 1) := by
    rw [cechPositiveVerticalHomologyIso_hom,
      cechPositiveVerticalHomologyIso_hom]
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g ↦ HomologicalComplex.homologyMap g (n + 1))
      (InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge_naturality U f phi).symm
  have hhorizontal :
      HomologicalComplex.homologyMap sectionsMap (n + 1) ≫
          (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).hom =
        (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).hom ≫
          HomologicalComplex.homologyMap totalMap (n + 1) := by
    rw [cechPositiveHorizontalHomologyIso_hom,
      cechPositiveHorizontalHomologyIso_hom]
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g ↦ HomologicalComplex.homologyMap g (n + 1))
      (HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge_naturality U f phi)
  have htotal := positiveIsoSquare_inv_naturality
    (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n)
    (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n)
    (HomologicalComplex.homologyMap sectionsMap (n + 1))
    (HomologicalComplex.homologyMap totalMap (n + 1)) hhorizontal
  have hderived :
      HomologicalComplex.homologyMap sectionsMap (n + 1) ≫
          (IG.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv =
        (IF.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv ≫
          ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
    exact cechPositiveDerived_naturality f phi n
  have hmiddle :
      HomologicalComplex.homologyMap totalMap (n + 1) ≫
          ((Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).inv ≫
            (IG.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv) =
        (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫
          ((IF.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv ≫
            ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).map f) := by
    calc
      _ = (HomologicalComplex.homologyMap totalMap (n + 1) ≫
            (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U G hU n).inv) ≫
            (IG.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv :=
        (Category.assoc _ _ _).symm
      _ = ((Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫
            HomologicalComplex.homologyMap sectionsMap (n + 1)) ≫
            (IG.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv := by
        rw [htotal]
      _ = (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫
            (HomologicalComplex.homologyMap sectionsMap (n + 1) ≫
              (IG.isoRightDerivedObj (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).inv) :=
        Category.assoc _ _ _
      _ = _ := congrArg
        (fun g ↦ (Comparison.TopCat.Sheaf.cechPositiveHorizontalHomologyIso U F hU n).inv ≫ g)
        hderived
  rw [cechPositiveRightDerivedIso_hom,
    cechPositiveRightDerivedIso_hom]
  simp only [← Category.assoc]
  rw [hvertical]
  simp only [Category.assoc]
  rw [hmiddle]
  rfl

/-- The positive-degree Čech comparison is natural in the coefficient sheaf. -/
theorem cechHomologySuccIsoOfAcyclicIntersections_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤)
    (hF : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F)
    (hG : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.hom) (n + 1) ≫
      (Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U G hU hG n).hom =
    (Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U F hU hF n).hom ≫
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) (n + 1)).map f := by
  rw [cechHomologySuccIsoOfAcyclicIntersections_hom,
    cechHomologySuccIsoOfAcyclicIntersections_hom]
  simp only [← Category.assoc]
  rw [cechPositiveRightDerivedIso_naturality
    U f hU hF hG n]
  simp only [Category.assoc]
  congr 1
  ext x
  exact Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections_symm_naturality f (n + 1) x

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.ComparisonNaturality.TopCat.Sheaf
