/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.CohomologyInjectiveModel
import OAI.Algebra.Homology.Notation

/-! # Cohomology Injective Restrict -/

namespace OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Naturality of the injective model in the pair

For `U' ≤ U` and `V' ≤ V`, the identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, I))` commutes
with the map of pairs on the left and with support enlargement followed by restriction on the
right.
-/

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace

variable (X : TopCat.{0})

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf
  TopCat.Sheaf.instAbelian

variable {U V W U' V' W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W')
  (hU : U' ≤ U) (hV : V' ≤ V) (hWW : W' ≤ W)

lemma pairSheafHomEvaluation_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomEvaluation X U' V' W' hW' G =
      CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomEvaluation X U V W hW G ≫ G.obj.map (homOfLE hV).op := by
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext (fun φ => ?_)
  exact OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafHomAddEquiv_pairSheafMap_comp
    (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
    (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) G φ

lemma pairSheafHomIsoSupportedSections_restrict (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.map (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
        (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)).op).app G ≫
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections X U' V' W' hW' G).hom =
      (CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections X U V W hW G).hom ≫
        ((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
          ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op := by
  apply (cancel_mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V'))).1
  have h1 : ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').obj G).obj.map (homOfLE hV).op ≫
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V') =
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) ≫
        G.obj.map (homOfLE hV).op :=
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.naturality (homOfLE hV).op
  have h2 : ((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V) ≫
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V) =
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V) := by
    change (((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G ≫
      (DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U').app G).hom.app (op V)) = _
    rw [← NatTrans.comp_app, DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap_inclusion]
  rw [Category.assoc, CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion,
    pairSheafHomEvaluation_restrict X hW hW' hV hWW, Category.assoc, Category.assoc, h1,
    ← Category.assoc (((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU).app G).hom.app (op V)), h2,
    ← Category.assoc, CohomologyInjectiveModel.TopCat.Sheaf.pairSheafHomIsoSupportedSections_hom_inclusion]

lemma homComplexPairSheafIsoSupportedSections_restrict
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ) :
    Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap ((CochainComplex.singleFunctor _ 0).map
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
          (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
          (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _))) K ≫
        (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U' V' W' hW' K).hom =
      (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections X U V W hW K).hom ≫
        CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K := by
  dsimp only [CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections, Iso.trans_hom]
  rw [← Category.assoc,
    Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap_single_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc, Category.assoc]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact pairSheafHomIsoSupportedSections_restrict X hW hW' hU hV hWW (K.X n)

variable [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

/-- The relative cohomology class obtained by restricting the pair before applying the
injective supported-section model. -/
def relativeClassAfterRestriction
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).obj
        I)).homology n :=
  CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    X U' V' W' hW' F I ι n
      (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F _ _
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x)

/-- The supported-section class obtained by enlarging support and restricting sections after
applying the injective model. -/
def supportedClassAfterRestriction
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).obj
        I)).homology n :=
  HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n
    (CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
      X U V W hW F I ι n x)

/-- The canonical morphism of pair sheaves induced by restriction of the ambient and supported
opens. -/
abbrev pairSheafRestriction :
    CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U' V' W' hW' ⟶
      CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW :=
  OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.pairSheafMap
    (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
    (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _)

/-- The Hom-complex cohomology class obtained from a relative Ext class after transport to a
K-injective resolution. -/
def injectiveHomComplexClass
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n
      (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)) I).homology n := by
  letI : IsIso (DerivedCategory.Q.map ι) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ι)).2 inferInstance
  exact (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm
    (Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ I n
      (Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv
        (Iso.refl (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
          (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW))))
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))
        (Ext.homAddEquiv x)))

/-- Restriction of a relative cohomology class is precomposition by the pair-sheaf map under the
derived-category description of Ext. -/
lemma relH_restrict_homAddEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n
      (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    Ext.homAddEquiv (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F
      (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
      (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (pairSheafRestriction
          X hW hW' hV hWW)) ≫ Ext.homAddEquiv x := by
  simp only [OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict,
    Ext.homAddEquiv_apply, Ext.bilinearComp_apply_apply, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp]
  rfl

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Transport to an injective resolution commutes with precomposition by the pair-sheaf map. -/
lemma isoHomCongrAddEquiv_pairSheafRestriction
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (y : ShiftedHom
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) (n : ℤ)) :
    Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv
      (Iso.refl (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U' V' W' hW'))))
      ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))
      (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (pairSheafRestriction
          X hW hW' hV hWW)) ≫ y) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (pairSheafRestriction
          X hW hW' hV hWW)) ≫
        Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv
          (Iso.refl (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
            (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW))))
          ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι))) y := by
  simp [Algebra.Homology.DerivedCategoryInjectiveHom.CategoryTheory.isoHomCongrAddEquiv_apply]

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- The inverse Hom-complex cohomology equivalence sends precomposition of classes to the
homology map of the precomposition chain map. -/
lemma homologyAddEquiv_symm_precomp
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    (n : ℕ)
    (c : CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor _ 0).obj
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)) I n) :
    (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm
      (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass
        ((CochainComplex.singleFunctor _ 0).map
          (pairSheafRestriction
            X hW hW' hV hWW)) I n c) =
      HomologicalComplex.homologyMap
        (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map
            (pairSheafRestriction
              X hW hW' hV hWW)) I) n
        ((CochainComplex.HomComplex.homologyAddEquiv _ I n).symm c) := by
  apply (CochainComplex.HomComplex.homologyAddEquiv _ I n).injective
  rw [Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.homologyAddEquiv_precompMap,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Transport to an injective Hom complex carries restriction of the pair to precomposition by
the pair-sheaf morphism. -/
lemma injectiveHomComplexClass_restrict
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι]
    (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n
      (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    injectiveHomComplexClass
      X hW' F I ι n
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F
          (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
          (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap
        (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map
            (pairSheafRestriction
              X hW hW' hV hWW)) I) n
        (injectiveHomComplexClass
          X hW F I ι n x) := by
  dsimp only [injectiveHomComplexClass]
  rw [relH_restrict_homAddEquiv
      X hW hW' hV hWW,
    isoHomCongrAddEquiv_pairSheafRestriction
      X hW hW' hV hWW,
    Algebra.Homology.DerivedCategoryInjectiveHom.CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_precomp,
    homologyAddEquiv_symm_precomp
      X hW hW' hV hWW]

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- On homology, precomposition followed by the pair-sheaf comparison is support enlargement
followed by section restriction. -/
lemma homComplexPairSheafIsoSupportedSections_homology_restrict
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map
            (pairSheafRestriction
              X hW hW' hV hWW)) I) n ≫
      HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
          X U' V' W' hW' I).hom n =
      HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
          X U V W hW I).hom n ≫
        HomologicalComplex.homologyMap
          (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    homComplexPairSheafIsoSupportedSections_restrict
      X hW hW' hU hV hWW I]

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Pointwise, the Hom-complex comparison carries pair restriction to support enlargement and
section restriction. -/
lemma homComplexPairSheafIsoSupportedSections_homology_restrict_apply
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    (n : ℕ)
    (z : (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj
        (CohomologyInjectiveModel.TopCat.Sheaf.pairSheaf' X U V W hW)) I).homology n) :
    (HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
          X U' V' W' hW' I).hom n).hom
      ((HomologicalComplex.homologyMap
        (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompMap
          ((CochainComplex.singleFunctor _ 0).map
            (pairSheafRestriction
              X hW hW' hV hWW)) I) n).hom z) =
      (HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction
          X hU hV I) n).hom
        ((HomologicalComplex.homologyMap
          (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
            X U V W hW I).hom n).hom z) := by
  have h := congrArg AddCommGrpCat.Hom.hom
    (homComplexPairSheafIsoSupportedSections_homology_restrict
      X hW hW' hU hV hWW I n)
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at h
  exact DFunLike.congr_fun h z

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The injective model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomology_restrict
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ)
    [I.IsKInjective] (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
      X U' V' W' hW' F I ι n
        (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F
          (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
          (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x) =
      HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n
        (CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
          X U V W hW F I ι n x) := by
  change (HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
        X U' V' W' hW' I).hom n).hom
      (injectiveHomComplexClass
        X hW' F I ι n
          (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F
            (homOfLE (hW ▸ inf_le_left : W ≤ V)) (homOfLE (hW' ▸ inf_le_left : W' ≤ V'))
            (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x)) =
    (HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV I) n).hom
      ((HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
          X U V W hW I).hom n).hom
        (injectiveHomComplexClass
          X hW F I ι n x))
  rw [injectiveHomComplexClass_restrict
      X hW hW' hV hWW F I ι n x,
    homComplexPairSheafIsoSupportedSections_homology_restrict_apply
      X hW hW' hU hV hWW I n]

end

end OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict.TopCat.Sheaf
