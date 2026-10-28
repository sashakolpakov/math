import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveSupportSheafNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison

/-! # Supported Injective Global Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalSquare

noncomputable section

/-! # The actual singular-to-injective comparison preserves support forgetting -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X))

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
theorem supportedInjectiveGlobal_square :
    ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex ℤᵘᵖ).map
        (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularToAmbientInjective X S.compl) ≫
      SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X) =
    SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ≫
      ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex ℤᵘᵖ).map
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
          (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)) := by
  let Y := TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)
  let Γ := (AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex ℤᵘᵖ
  let f := AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex Y (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X)
  have h := ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y S.compl).mapHomologicalComplex
    ℤᵘᵖ).naturality f
  simpa only [CategoryTheory.Functor.map_comp] using! congrArg (Γ.map) h

theorem supportedInjectiveGlobal_class (n : ℤ)
    (a : ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (AlgebraicTopology.Support.SingularFlasqueModel.Singular.supportedRationalSingularCochainComplex
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl))).homology n) :
    homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveComplex X)) n
      ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ n).hom a) =
    homologyMap
      (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) ⊤).mapHomologicalComplex ℤᵘᵖ).map
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.singularToConstantInjectiveComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
          (ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X))) n
      (homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S.compl
        (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))) n a) := by
  simpa only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] using!
    ConcreteCategory.congr_hom (congrArg (fun f => homologyMap f n)
      (supportedInjectiveGlobal_square X S)) a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalSquare
