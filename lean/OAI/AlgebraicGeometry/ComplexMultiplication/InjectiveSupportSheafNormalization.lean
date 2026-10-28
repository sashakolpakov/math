import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedSingularSheafNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SectionCohomologySheafNaturality
import OAI.AlgebraicGeometry.Cycle.FundamentalClass

/-! # Injective Support Sheaf Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveSupportSheafNormalization

noncomputable section

/-! # The original injective support comparison preserves actual local relative classes -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)
  (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem injectiveSupportSheaf_normalization :
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S) (n : ℤ) V ≫
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V) =
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S n).app (op V) := by
  let : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X
  let f := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X S.compl
  let e := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  rw [← cancel_epi e.hom]
  have hn := SectionCohomologySheafNaturality.sectionCohomologyToSheafSection_naturality
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) f (n : ℤ) V
  have he : e.hom = homologyMap
      (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) V).mapHomologicalComplex ℤᵘᵖ).map f)
      (n : ℤ) := rfl
  have hn' : e.hom ≫ AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveComplex X S) (n : ℤ) V =
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)
        (n : ℤ) V ≫ (homologyMap f (n : ℤ)).hom.app (op V) := by
    simpa only [he] using! hn
  change e.hom ≫ _ ≫ _ = e.hom ≫ _ ≫ _
  have hi : (homologyMap f (n : ℤ)).hom.app (op V) ≫
      (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V) =
      (AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        S S.isClosed n).hom.hom.app (op V) := by
    change ((homologyMap f (n : ℤ)) ≫
      (asIso (homologyMap f (n : ℤ))).inv ≫
        (AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
          S S.isClosed n).hom).hom.app (op V) = _
    simp
  calc
    _ = AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)
        (n : ℤ) V ≫ (homologyMap f (n : ℤ)).hom.app (op V) ≫
          (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V) := by
      simpa only [Category.assoc] using! (congrArg (fun g => g ≫
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V)) hn')
    _ = AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)
        (n : ℤ) V ≫
          (AlgebraicTopology.Support.SingularCohomologySheafComparison.Singular.supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
            S S.isClosed n).hom.hom.app (op V) := by
      exact congrArg (fun g => AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl)
        (n : ℤ) V ≫ g) hi
    _ = _ := by
      have hc : e.hom ≫
          (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
          (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S n).app (op V) =
          (AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed V n).toAddCommGrpIso.hom ≫
          (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S n).app (op V) := by
        ext a
        change (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S n).app (op V)
          ((AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement
            (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed V n) (e.inv (e.hom a))) = _
        have hea : e.inv (e.hom a) = a :=
          congrArg (fun g => g a) e.hom_inv_id
        rw [hea]
        rfl
      apply Eq.trans _ hc.symm
      simpa only using! SupportedSingularSheafNormalization.supportedSingularSheaf_normalization
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S S.isClosed n V

end

end OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveSupportSheafNormalization
