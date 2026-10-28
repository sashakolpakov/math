import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison

/-! # Edge Homology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.EdgeHomologyNaturality.IntrinsicCech

noncomputable section

/-! Naturality of the homology maps used in the positive-degree Čech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
universe u
variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)
local instance : (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

theorem isoSquare_inv_naturality
    {A B C D : AddCommGrpCat.{u}} (e : A ≅ B) (e' : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  rw [e'.comp_inv_eq, Category.assoc, h]
  simp

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (phi : InjectiveResolution.Hom (injectiveResolution F) (injectiveResolution G) f)

theorem cechPositiveVerticalHomologyIso_naturality
    (hF : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U F) (hG : AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) ≫
        (IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso U G hG n).hom =
      (IntrinsicCech.SheafCohomologyComparison.cechPositiveVerticalHomologyIso U F hF n).hom ≫
        HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom) (n + 1) := by
  change HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) ≫
      HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U G) (n + 1) =
    HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge U F) (n + 1) ≫
      HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom) (n + 1)
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
    (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionVerticalEdge_naturality U f phi).symm

theorem cechPositiveHorizontalHomologyIso_naturality
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    HomologicalComplex.homologyMap (ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom) (n + 1) ≫
        (IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso U G hU n).hom =
      (IntrinsicCech.SheafCohomologyComparison.cechPositiveHorizontalHomologyIso U F hU n).hom ≫
        HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom) (n + 1) := by
  change HomologicalComplex.homologyMap (ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom) (n + 1) ≫
      HomologicalComplex.homologyMap (ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge U G) (n + 1) =
    HomologicalComplex.homologyMap (ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge U F) (n + 1) ≫
      HomologicalComplex.homologyMap (InjectiveVerticalEdge.IntrinsicCech.cechInjectiveResolutionTotalMap U phi.hom) (n + 1)
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun g => HomologicalComplex.homologyMap g (n + 1))
    (ResolutionHorizontalComparison.IntrinsicCech.cechResolutionHorizontalEdge_naturality U f phi)

theorem cechResolutionDerived_naturality (n : ℕ) :
    HomologicalComplex.homologyMap (ResolutionSections.IntrinsicCech.cechResolutionSectionsMap phi.hom) (n + 1) ≫
        ((injectiveResolution G).isoRightDerivedObj (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)).inv =
      ((injectiveResolution F).isoRightDerivedObj (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)).inv ≫
        ((TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X).rightDerived (n + 1)).map f := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution F) (injectiveResolution G) phi.hom
    phi.ι_f_zero_comp_hom_f_zero (TopologicalSheafCohomology.IntrinsicCech.globalSectionsFunctor X) (n + 1)
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.EdgeHomologyNaturality.IntrinsicCech
