import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyClassNaturality

/-! # Global Hypercohomology Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalHypercohomologyNaturality

noncomputable section

/-! # Genuine inverse image of the original global cohomology comparison -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.CochainComplex.HomComplex

variable {X Y : Over (Spec (.of ℂ))}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original global cohomology class map commutes with scheme inverse image. -/
theorem globalSectionsToHomComplexClass_inverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (x : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) K).homology n) :
    GlobalNaturality.globalSectionsToHomComplexClass X ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
        (HomologicalComplex.homologyMap (GlobalPullback.originalGlobalSectionsComplexInverseImage f K) n x) =
      HomPullback.originalHomComplexClassInverseImage f K n (GlobalNaturality.globalSectionsToHomComplexClass Y K n x) := by
  let eY := Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) K
  let eX := Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
    ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K)
  have h : eY.inv ≫ GlobalPullback.originalHomComplexInverseImageMap f K =
      GlobalPullback.originalGlobalSectionsComplexInverseImage f K ≫ eX.inv := by
    apply (cancel_mono eX.hom).1
    rw [Category.assoc, GlobalPullback.originalHomComplexGlobalSections_inverseImage]
    change eY.inv ≫ eY.hom ≫ GlobalPullback.originalGlobalSectionsComplexInverseImage f K =
      (GlobalPullback.originalGlobalSectionsComplexInverseImage f K ≫ eX.inv) ≫ eX.hom
    rw [eY.inv_hom_id_assoc, Category.assoc, eX.inv_hom_id]
    exact (Category.comp_id _).symm
  have hh : HomologicalComplex.homologyMap (GlobalPullback.originalHomComplexInverseImageMap f K) n
      (HomologicalComplex.homologyMap eY.inv n x) =
    HomologicalComplex.homologyMap eX.inv n
      (HomologicalComplex.homologyMap (GlobalPullback.originalGlobalSectionsComplexInverseImage f K) n x) := by
    simpa only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] using!
      ConcreteCategory.congr_hom
        (congrArg (fun g => HomologicalComplex.homologyMap g n) h) x
  change homologyAddEquiv _ _ n
      (HomologicalComplex.homologyMap eX.inv n
        (HomologicalComplex.homologyMap (GlobalPullback.originalGlobalSectionsComplexInverseImage f K) n x)) =
    HomPullback.originalHomComplexClassInverseImage f K n
      (homologyAddEquiv _ K n (HomologicalComplex.homologyMap eY.inv n x))
  rw [← hh]
  exact GlobalPullback.homologyAddEquiv_originalHomComplexInverseImage f K n _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged global-to-hypercohomology comparison commutes with actual scheme pullback. -/
theorem globalSectionsToHypercohomology_inverseImage (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (x : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) K).homology n) :
    GlobalNaturality.globalSectionsToHypercohomology X ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
        (HomologicalComplex.homologyMap (GlobalPullback.originalGlobalSectionsComplexInverseImage f K) n x) =
      HypercohomologyPullback.originalHypercohomologyPullback f K n (GlobalNaturality.globalSectionsToHypercohomology Y K n x) := by
  change GlobalNaturality.homComplexClassToHypercohomology X _ n
    (GlobalNaturality.globalSectionsToHomComplexClass X _ n
      (HomologicalComplex.homologyMap (GlobalPullback.originalGlobalSectionsComplexInverseImage f K) n x)) = _
  exact (congrArg (GlobalNaturality.homComplexClassToHypercohomology X _ n)
      (globalSectionsToHomComplexClass_inverseImage f K n x)).trans
    (HypercohomologyClassNaturality.originalHypercohomologyPullback_homComplexClass f K n
      (GlobalNaturality.globalSectionsToHomComplexClass Y K n x)).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalHypercohomologyNaturality
