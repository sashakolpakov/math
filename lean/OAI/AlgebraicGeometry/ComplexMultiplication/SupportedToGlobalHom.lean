import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality
import OAI.CategoryTheory.Sites.SheafCohomologyPair
import OAI.AlgebraicTopology.Support.CohomologyInjectiveModel

/-! # Supported To Global Hom -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom

noncomputable section

section

/-! # Evaluation of the terminal free sheaf is evaluation at the constant integer one -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace

variable (Y : TopCat.{0})

theorem sheafification_map_unit_apply
    {P Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat} (η : P ⟶ Q) (U : Opens Y)
    (z : P.obj (op U)) :
    ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map η).hom.app (op U)
        ((toSheafify (Opens.grothendieckTopology Y) P).app (op U) z) =
      (toSheafify (Opens.grothendieckTopology Y) Q).app (op U) (η.app (op U) z) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Opens.grothendieckTopology Y) η) (op U)) z).symm

/-- The actual terminal free-integer sheaf and constant-integer sheaf comparison. -/
def integerToTerminalFreeSheafIso :
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ≅
      (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).obj ⊤ :=
  ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).mapIso (AddEquiv.ulift (α := ℤ)).toAddCommGrpIso).symm ≪≫
    (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafTerminalIso (J := Opens.grothendieckTopology Y)
      isTerminalTop).symm

theorem integerToTerminalFreeSheafIso_evaluation (F : TopCat.Sheaf AddCommGrpCat Y)
    (φ : (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology Y)).obj ⊤ ⟶ F) :
    Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections F
      ((integerToTerminalFreeSheafIso Y).hom ≫ φ) =
    OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafHomAddEquiv ⊤ F φ := by
  simp only [Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections,
    AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_apply,
    OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheafHomAddEquiv_apply]
  change φ.hom.app (op ⊤) _ = φ.hom.app (op ⊤) _
  congr 1
  let η := (Functor.const (Opens Y)ᵒᵖ).map
    (AddCommGrpCat.ofHom (AddEquiv.ulift (α := ℤ)).symm.toAddMonoidHom)
  let e : yoneda.obj (⊤ : Opens Y) ⋙ AddCommGrpCat.free ≅
      (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) :=
    NatIso.ofComponents
      (fun W =>
        letI : Unique (W.unop ⟶ (⊤ : Opens Y)) :=
          ⟨⟨isTerminalTop.from _⟩, fun _ => isTerminalTop.hom_ext _ _⟩
        ((FreeAbelianGroup.uniqueEquiv (W.unop ⟶ (⊤ : Opens Y))).trans
          AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro W V f
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro h
        rfl)
  change ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map e.inv).hom.app
      (op ⊤) (((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map η).hom.app
        (op ⊤) ((toSheafify (Opens.grothendieckTopology Y)
          ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ))).app (op ⊤) (1 : ℤ))) =
    (toSheafify (Opens.grothendieckTopology Y) (yoneda.obj ⊤ ⋙ AddCommGrpCat.free)).app
      (op ⊤) (FreeAbelianGroup.of (𝟙 ⊤))
  rw [sheafification_map_unit_apply, sheafification_map_unit_apply]
  congr 1

end

/-! # The actual inclusion of supported sections evaluates the pair generator -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Sheaf _root_.CochainComplex.HomComplex _root_.HomologicalComplex

variable (Y : TopCat.{0}) (U : Opens Y)

/-- The actual constant integer generator followed by the original pair quotient. -/
def integerToSupportPairSheaf :
    (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶
      AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' Y U ⊤ U (top_inf_eq U) :=
  (integerToTerminalFreeSheafIso Y).hom ≫
    cokernel.π ((OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.freeAbelianSheaf
      (Opens.grothendieckTopology Y)).map (homOfLE (le_top : U ≤ ⊤)))

/-- The literal support-forgetting inclusion on complexes of global sections. -/
def supportedToGlobalSectionComplex
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat) ℤ) :
    (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y U).mapHomologicalComplex ℤᵘᵖ).obj K)) ⟶
      Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y K :=
  ((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex ℤᵘᵖ).map
    (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y U).mapHomologicalComplex ℤᵘᵖ).app K)

theorem supportedToGlobalHomComplex_comparison
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat) ℤ) :
    Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap ((CochainComplex.singleFunctor _ 0).map (integerToSupportPairSheaf Y U)) K ≫
      (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K).hom =
    (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) K).hom ≫
      supportedToGlobalSectionComplex Y U K := by
  dsimp only [Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections,
    AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [← Category.assoc, Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc]
  simp only [Category.assoc]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change (preadditiveCoyoneda.map (integerToSupportPairSheaf Y U).op).app (K.X n) ≫
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections (K.X n)).toAddCommGrpIso.hom =
    (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections Y U ⊤ U (top_inf_eq U) (K.X n)).hom ≫
      ((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y U).app (K.X n)).hom.app (op ⊤)
  rw [AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion]
  apply AddCommGrpCat.hom_ext
  ext φ
  exact integerToTerminalFreeSheafIso_evaluation Y (K.X n)
    (cokernel.π _ ≫ φ)

theorem supportedToGlobalHomComplex_class
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat) ℤ) (n : ℤ)
    (z : ((((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (((AlgebraicTopology.Support.DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside Y U).mapHomologicalComplex ℤᵘᵖ).obj K))).homology n) :
    homologyAddEquiv (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex Y) K n
      (homologyMap (Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K).inv n
        (homologyMap (supportedToGlobalSectionComplex Y U K) n z)) =
    Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass ((CochainComplex.singleFunctor _ 0).map (integerToSupportPairSheaf Y U)) K n
      (homologyAddEquiv _ K n
        (homologyMap (AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) K).inv
          n z)) := by
  let eS := AlgebraicTopology.Support.CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections Y U ⊤ U (top_inf_eq U) K
  let eG := Cohomology.GlobalSections.TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y K
  let g := (CochainComplex.singleFunctor _ 0).map (integerToSupportPairSheaf Y U)
  have h : eS.inv ≫ Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap g K = supportedToGlobalSectionComplex Y U K ≫ eG.inv := by
    apply (cancel_mono eG.hom).1
    rw [Category.assoc, supportedToGlobalHomComplex_comparison Y U K]
    rw [eS.inv_hom_id_assoc, Category.assoc, eG.inv_hom_id, Category.comp_id]
  have hz := ConcreteCategory.congr_hom
    (congrArg (fun f => homologyMap f n) h) z
  simp only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] at hz
  calc
    _ = homologyAddEquiv (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex Y) K n
      (homologyMap (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap g K) n (homologyMap eS.inv n z)) :=
        congrArg (homologyAddEquiv (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex Y) K n) hz.symm
    _ = _ := Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.homologyAddEquiv_precompMap g K n _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom
