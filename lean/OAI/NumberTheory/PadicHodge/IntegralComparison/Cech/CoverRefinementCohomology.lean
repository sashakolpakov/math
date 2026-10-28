import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinement

/-! # Cover Refinement Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementCohomology

noncomputable section

/-! Refining an acyclic cover preserves the original comparison
from Čech cohomology to sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

private theorem square {C : Type*} [Category* C]
    {A B P Q D Z : C} (a : A ⟶ P) (b : B ⟶ Q) (m : A ⟶ B) (t : P ⟶ Q)
    (eP : D ≅ P) (eQ : D ≅ Q) (k : D ⟶ Z)
    (hv : a ≫ t = m ≫ b) (hh : eP.hom ≫ t = eQ.hom) :
    m ≫ (b ≫ eQ.inv ≫ k) = a ≫ eP.inv ≫ k := by
  have h : m ≫ b ≫ eQ.inv = a ≫ eP.inv := by
    apply (cancel_mono eQ.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hh]
    simp only [Iso.inv_hom_id_assoc]
    exact hv.symm
  simpa only [Category.assoc] using congrArg (fun z => z ≫ k) h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X : TopCat.{u}} {ι κ : Type u} (U : ι → Opens X) (V : κ → Opens X)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (haV : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic V F) (n : ℕ)

local instance : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

theorem rightDerived :
    HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) (n + 1) ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso V F hV haV n).hom =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveRightDerivedIso U F hU haU n).hom := by
  have hv := congrArg (fun a => HomologicalComplex.homologyMap a (n + 1))
    (CoverRefinement.vertical U V r F)
  have hh := congrArg (fun a => HomologicalComplex.homologyMap a (n + 1))
    (CoverRefinement.horizontal U V r F)
  simp only [HomologicalComplex.homologyMap_comp] at hv hh
  exact square
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso U F haU n).hom
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso V F haV n).hom
    (HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) (n + 1))
    (HomologicalComplex.homologyMap (CoverRefinement.totalMap U V r F) (n + 1))
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso U F hU n)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso V F hV n)
    ((injectiveResolution F).isoRightDerivedObj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)).inv hv hh

theorem cohomology :
    HomologicalComplex.homologyMap (CoverRefinement.map U V r F.obj) (n + 1) ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections V F hV haV n).hom =
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U F hU haU n).hom := by
  let e : ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).obj F ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj F :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.DerivedGlobalSections.DerivedSections.sheafCohomologyAddEquivRightDerived F (n + 1)).symm.toAddCommGrpIso
  have h := congrArg
    (fun a => a ≫ e.hom)
    (CoverRefinementCohomology.rightDerived U V r F hU hV haU haV n)
  simpa only [AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections, Iso.trans_hom, Category.assoc] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementCohomology
