import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DerivedComparisonNaturality

/-! # Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CohomologyNaturality.IntrinsicCech

noncomputable section

/-! The native acyclic-cover Čech comparison with genuine Ext sheaf cohomology is natural in every positive degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

theorem cechHomologySuccIsoOfAcyclicIntersections_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (hU : ⨆ i, U i = ⊤)
    (hF : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (hG : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) ≫
        (IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U G hU hG n).hom =
      (IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U F hU hF n).hom ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).map f := by
  apply ConcreteCategory.hom_ext
  intro x
  have hd := ConcreteCategory.congr_hom
    (DerivedComparisonNaturality.IntrinsicCech.cechPositiveRightDerivedIso_naturality U f hU hF hG n) x
  change (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.sheafCohomologyAddEquivRightDerived G (n + 1)).symm
      ((IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U G hU hG n).hom
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) x)) = _
  change (IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U G hU hG n).hom
      (HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) x) =
    ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).map f
      ((IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U F hU hF n).hom x) at hd
  exact (congrArg
    (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.sheafCohomologyAddEquivRightDerived G (n + 1)).symm hd).trans
      (HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.sheafCohomologyAddEquivRightDerived_symm_naturality f (n + 1)
        ((IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U F hU hF n).hom x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CohomologyNaturality.IntrinsicCech
