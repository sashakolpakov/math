import OAI.AlgebraicGeometry.ComplexMultiplication.HomDerivedPrecomp
import OAI.AlgebraicTopology.Support.CohomologyInjectiveModel

/-! # Supported Injective Derived Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass

noncomputable section

/-! # The original supported injective model represents the original Ext morphism -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace
open _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

variable (Y : TopCat.{0}) (U : Opens Y)
  [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)]

local instance CMSupportedInjectiveDerivedClass.localInstance1 :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) :=
  HasDerivedCategory.standard _

theorem supportedInjectiveDerivedClass
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (b : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (le_top : U ≤ ⊤))) :
    HomPostcomp.cohomologyClassToDerived _ I (n : ℤ)
      (homologyAddEquiv _ I (n : ℤ)
        (homologyMap (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) I).inv
          (n : ℤ) (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y U ⊤ U (top_inf_eq U) F I ι n b))) =
      Ext.homAddEquiv b ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧' := by
  let : IsIso (DerivedCategory.Q.map ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ι)).2 inferInstance
  have h : homologyAddEquiv _ I (n : ℤ)
      (homologyMap (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) I).inv
        (n : ℤ) (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y U ⊤ U (top_inf_eq U) F I ι n b)) =
    Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
      ((CochainComplex.singleFunctor _ 0).obj (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq U))) I (n : ℤ)
      (Ext.homAddEquiv b ≫ (DerivedCategory.Q.map ι)⟦(n : ℤ)⟧') := by
    let A := (CochainComplex.singleFunctor _ 0).obj (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq U))
    let e := homologyMapIso (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) I)
      (n : ℤ)
    let c := Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass A I (n : ℤ)
      (Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj A))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))
        (Ext.homAddEquiv b))
    change homologyAddEquiv A I (n : ℤ)
      (e.inv (e.hom ((homologyAddEquiv A I (n : ℤ)).symm c))) = _
    have he : e.inv (e.hom ((homologyAddEquiv A I (n : ℤ)).symm c)) =
        (homologyAddEquiv A I (n : ℤ)).symm c :=
      ConcreteCategory.congr_hom e.hom_inv_id _
    rw [he, AddEquiv.apply_symm_apply]
    dsimp only [c, Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv_apply, Iso.refl_inv, Functor.mapIso_hom, asIso_hom]
    rw [Category.id_comp]
  rw [h, HomPostcomp.cohomologyClassToDerived_kInjective]
  exact (Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
    ((CochainComplex.singleFunctor _ 0).obj (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq U)))
    I (n : ℤ)).symm_apply_apply _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedInjectiveDerivedClass
