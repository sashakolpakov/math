import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionHorizontalComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ResolutionVerticalComparison

/-! # Sheaf Cohomology Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison

noncomputable section

/-! Acyclic-cover Čech comparison in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

noncomputable local instance comparisonSections_additive :
    (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

/-- The vertical map identifies Čech cohomology with the cohomology of the total complex. -/
def cechPositiveVerticalHomologyIso (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hH : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      ((Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology (n + 1) := by
  have : QuasiIsoAt (Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U F) (n + 1) :=
    Cech.ResolutionVerticalComparison.IntrinsicCech.cechInjectiveResolutionVerticalEdge_quasiIsoAt_succ U F hH n
  exact asIso (HomologicalComplex.homologyMap
    (Cech.InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U F) (n + 1))

/-- The horizontal map identifies derived global sections with the cohomology
of the same total complex. -/
def cechPositiveHorizontalHomologyIso (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Cech.ResolutionSections.IntrinsicCech.cechResolutionSectionsComplex F).homology (n + 1) ≅
      ((Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology (n + 1) := by
  have : QuasiIsoAt (Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge U F) (n + 1) :=
    Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge_quasiIsoAt_succ U F hU n
  exact asIso (HomologicalComplex.homologyMap
    (Cech.ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge U F) (n + 1))

/-- The actual Čech complex computes derived global sections on an acyclic cover. -/
def cechPositiveRightDerivedIso (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) (hH : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).obj F :=
  cechPositiveVerticalHomologyIso U F hH n ≪≫
    (cechPositiveHorizontalHomologyIso U F hU n).symm ≪≫
    ((injectiveResolution F).isoRightDerivedObj
      (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)).symm

/-- An actual open cover with acyclic tuple intersections computes genuine
sheaf Ext cohomology in every positive degree. -/
def cechHomologySuccIsoOfAcyclicIntersections (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hU : ⨆ i, U i = ⊤) (hH : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) (n + 1)).obj F :=
  cechPositiveRightDerivedIso U F hU hH n ≪≫
    (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.sheafCohomologyAddEquivRightDerived F (n + 1)).symm.toAddCommGrpIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison
