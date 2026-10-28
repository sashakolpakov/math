import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass

/-! # Supported Injective Global Derived -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived

noncomputable section

/-! # The derived morphism of the actual support-forgetting inclusion -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf TopCat.Sheaf.instAbelian

variable (Y : TopCat.{0}) (U : Opens Y)
  [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)]
local instance CMSupportedInjectiveGlobalDerived.localInstance1 : HasDerivedCategory
    (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) :=
  HasDerivedCategory.standard _
local instance CMSupportedInjectiveGlobalDerived.localInstance2 : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _

theorem supportedInjectiveGlobalDerivedClass
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (b : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (le_top : U ≤ ⊤))) :
    HomPostcomp.cohomologyClassToDerived (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex Y) I (n : ℤ)
      (homologyAddEquiv _ I (n : ℤ)
        (homologyMap (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y I).inv (n : ℤ)
          (homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex Y U I) (n : ℤ)
            (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y U ⊤ U (top_inf_eq U) F I ι n b)))) =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
      (SupportedToGlobalHom.integerToSupportPairSheaf Y U)) ≫
      Ext.homAddEquiv b ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' := by
  rw [SupportedToGlobalHom.supportedToGlobalHomComplex_class]
  have hd := HomDerivedPrecomp.cohomologyClassToDerived_precomp
    ((CochainComplex.singleFunctor _ 0).map (SupportedToGlobalHom.integerToSupportPairSheaf Y U))
    (n : ℤ) (homologyAddEquiv _ I (n : ℤ)
      (homologyMap (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U
        (top_inf_eq U) I).inv (n : ℤ)
        (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y U ⊤ U (top_inf_eq U) F I ι n b)))
  simpa only [] using! hd.trans
    (congrArg (fun z => DerivedCategory.Q.map
      ((CochainComplex.singleFunctor _ 0).map (SupportedToGlobalHom.integerToSupportPairSheaf Y U)) ≫ z)
      (SupportedInjectiveDerivedClass.supportedInjectiveDerivedClass Y U F I ι n b))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveGlobalDerived
