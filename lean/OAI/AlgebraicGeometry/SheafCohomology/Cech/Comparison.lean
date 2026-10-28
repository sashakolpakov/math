import OAI.AlgebraicGeometry.SheafCohomology.Cech.HorizontalComparison
import OAI.AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-! Acyclic-cover Čech comparison in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

noncomputable local instance e35ComparisonSections_additive :
    (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- The vertical map identifies Čech cohomology with the cohomology of the total complex. -/
def cechPositiveVerticalHomologyIso (F : Sheaf AddCommGrpCat.{u} X)
    (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology (n + 1) := by
  have : QuasiIsoAt (InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1) :=
    VerticalComparison.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge_quasiIsoAt_succ U F hH n
  exact asIso (HomologicalComplex.homologyMap
    (InjectiveAugmentation.TopCat.Sheaf.cechInjectiveResolutionVerticalEdge U F) (n + 1))

/-- The horizontal map identifies derived global sections with the cohomology
of the same total complex. -/
def cechPositiveHorizontalHomologyIso (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (HorizontalComparison.TopCat.Sheaf.cechResolutionSectionsComplex F).homology (n + 1) ≅
      ((InjectiveBicomplex.TopCat.Sheaf.cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology (n + 1) := by
  have : QuasiIsoAt (HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F) (n + 1) :=
    HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge_quasiIsoAt_succ U F hU n
  exact asIso (HomologicalComplex.homologyMap
    (HorizontalComparison.TopCat.Sheaf.cechResolutionHorizontalEdge U F) (n + 1))

/-- The actual Čech complex computes derived global sections on an acyclic cover. -/
def cechPositiveRightDerivedIso (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      ((GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived (n + 1)).obj (Compat.TopCat.Sheaf.toSiteSheaf F) :=
  cechPositiveVerticalHomologyIso U F hH n ≪≫
    (cechPositiveHorizontalHomologyIso U F hU n).symm ≪≫
    ((injectiveResolution (Compat.TopCat.Sheaf.toSiteSheaf F)).isoRightDerivedObj
      (GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X) (n + 1)).symm

/-- An actual open cover with acyclic tuple intersections computes genuine
sheaf Ext cohomology in every positive degree. -/
def cechHomologySuccIsoOfAcyclicIntersections (F : Sheaf AddCommGrpCat.{u} X)
    (hU : ⨆ i, U i = ⊤) (hH : VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) (n + 1)).obj F :=
  cechPositiveRightDerivedIso U F hU hH n ≪≫
    (Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F (n + 1)).symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison.TopCat.Sheaf
