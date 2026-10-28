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
import OAI.AlgebraicTopology.Support.CohomologyFlasqueModel
import OAI.AlgebraicTopology.Support.CohomologyInjectiveRestrict
import OAI.Algebra.Homology.Notation

/-! # Cohomology Flasque Restrict -/

namespace OAI.AlgebraicTopology.Support.CohomologyFlasqueRestrict.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Naturality of the flasque model in the pair

The identification `H^n(V, V ⊓ U; F) ≃ H^n(Γ_{X ∖ U}(V, K))` commutes with the map of pairs and
with support enlargement followed by restriction.
-/

open _root_.CategoryTheory Limits Abelian Opposite _root_.TopologicalSpace

variable (X : TopCat.{0})

variable {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)

lemma supportedSectionsRestriction_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat X) ℤ} (φ : K ⟶ L) :
    CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K ≫
        ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
          (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ) =
      ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map φ) ≫
        CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV L := by
  have h1 := (NatTrans.mapHomologicalComplex (SectionRestrictionCone.TopCat.Sheaf.supportEvaluationRestriction X (homOfLE hV))
    ℤᵘᵖ).naturality (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map φ)
  have h2 := (NatTrans.mapHomologicalComplex (DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X hU)
    ℤᵘᵖ).naturality φ
  dsimp only [CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction, SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction]
  simp only [Category.assoc]
  rw [← h1]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← h2]

variable {W W' : Opens X} (hW : V ⊓ U = W) (hW' : V' ⊓ U' = W') (hWW : W' ≤ W)
  (F : Sheaf AddCommGrpCat X) (K : CochainComplex (Sheaf AddCommGrpCat X) ℤ) [K.IsStrictlyGE 0]
  (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ K) [Mono ι] [QuasiIso ι]
  (hK : ∀ n, IsFlasque (K.X n))

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf
  TopCat.Sheaf.instAbelian

variable [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

/-- The relative class obtained by restricting the pair before applying a flasque supported-section
model. -/
def flasqueRelativeClassAfterRestriction
    (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n
      (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).obj
        K)).homology n :=
  CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque
    X F K ι U' V' W' hW' hK n
      (OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH.restrict F _ _
        (homOfLE hWW) (homOfLE hV) (Subsingleton.elim _ _) n x)

/-- The flasque supported-section class obtained by enlarging support and restricting sections. -/
def flasqueSupportedClassAfterRestriction
    (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n
      (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).obj
        K)).homology n :=
  HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n
    (CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque
      X F K ι U V W hW hK n x)

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- The comparison from a flasque resolution to the canonical injective resolution commutes on
homology with support enlargement and section restriction. -/
lemma supportedSectionsResolution_homology_naturality
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n ≫
      HomologicalComplex.homologyMap
        (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V').mapHomologicalComplex ℤᵘᵖ).map
          (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U').mapHomologicalComplex ℤᵘᵖ).map
            (CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n =
      HomologicalComplex.homologyMap
        (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
          (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
            (CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n ≫
        HomologicalComplex.homologyMap
          (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    supportedSectionsRestriction_naturality]

/-- The quasi-isomorphism from a flasque resolution to the canonical injective resolution after
taking supported-section cohomology. -/
def supportedSectionsResolutionHomologyIso
    (U V : Opens X) (n : ℕ) :
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K)).homology n ≅
      (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
          (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F))).homology n := by
  letI := CohomologyFlasqueModel.TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso
    X F K ι U V hK
  exact asIso (HomologicalComplex.homologyMap
    (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).map
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).map
        (CohomologyFlasqueModel.TopCat.Sheaf.resolutionToInjective X F K ι))) n)

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Inverting the flasque-to-injective comparison preserves its naturality with respect to the
pair. -/
lemma supportedSectionsResolution_homology_inverse_naturality
    (n : ℕ) :
    (supportedSectionsResolutionHomologyIso
      X F K ι hK U V n).inv ≫
      HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n =
      HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n ≫
        (supportedSectionsResolutionHomologyIso
          X F K ι hK U' V' n).inv := by
  let e := supportedSectionsResolutionHomologyIso
    X F K ι hK U V n
  let e' := supportedSectionsResolutionHomologyIso
    X F K ι hK U' V' n
  change e.inv ≫ HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n =
    HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
        (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n ≫ e'.inv
  have h := supportedSectionsResolution_homology_naturality
    X hU hV F K ι n
  change HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n ≫ e'.hom =
    e.hom ≫ HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
        (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n at h
  apply (Iso.inv_comp_eq e).2
  rw [← Category.assoc, ← h, Category.assoc, e'.hom_inv_id, Category.comp_id]

omit [HasExt (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] in
/-- Pointwise, the inverse resolution comparison carries support enlargement and section
restriction across the flasque and injective models. -/
lemma supportedSectionsResolution_homology_inverse_naturality_apply
    (n : ℕ)
    (z : (((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
        (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F))).homology n) :
    (supportedSectionsResolutionHomologyIso
      X F K ι hK U' V' n).inv.hom
      ((HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
          (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n).hom z) =
      (HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n).hom
        ((supportedSectionsResolutionHomologyIso
          X F K ι hK U V n).inv.hom z) := by
  have h := congrArg AddCommGrpCat.Hom.hom
    (supportedSectionsResolution_homology_inverse_naturality
      X hU hV F K ι hK n)
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at h
  exact (DFunLike.congr_fun h z).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque model is natural in the pair. -/
theorem relHAddEquivSupportedSectionsHomologyOfFlasque_restrict (n : ℕ)
    (x : OAI.CategoryTheory.Sites.SheafCohomologyPair.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V))) :
    flasqueRelativeClassAfterRestriction
      (X := X) (hV := hV) (hW := hW) (hW' := hW') (hWW := hWW) F K ι hK n x =
      flasqueSupportedClassAfterRestriction
        (X := X) (hU := hU) (hV := hV) (hW := hW) F K ι hK n x := by
  have := CohomologyFlasqueModel.TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso X F K ι U V hK
  have := CohomologyFlasqueModel.TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso X F K ι U' V' hK
  have : (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F).IsKInjective :=
    CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex_isKInjective X F
  have : QuasiIso (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) :=
    CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso X F
  dsimp only [flasqueRelativeClassAfterRestriction,
    flasqueSupportedClassAfterRestriction,
    CohomologyFlasqueModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque, AddEquiv.trans_apply]
  rw [@CohomologyInjectiveRestrict.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_restrict X U V W U' V' W' hW hW' hU hV hWW _ F
    (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F) (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex_isKInjective X F)
    (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso X F) n x,
    Iso.addCommGroupIsoToAddEquiv_apply, Iso.addCommGroupIsoToAddEquiv_apply, Iso.symm_hom,
    Iso.symm_hom]
  change (supportedSectionsResolutionHomologyIso
      X F K ι hK U' V' n).inv.hom
      ((HomologicalComplex.homologyMap
        (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV
          (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)) n).hom
        (CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
          X U V W hW F
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) n x)) =
    (HomologicalComplex.homologyMap
      (CohomologyInjectiveModel.TopCat.Sheaf.supportedSectionsRestriction X hU hV K) n).hom
      ((supportedSectionsResolutionHomologyIso
        X F K ι hK U V n).inv.hom
        (CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
          X U V W hW F
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)
            (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) n x))
  exact supportedSectionsResolution_homology_inverse_naturality_apply
    X hU hV F K ι hK n
      (CohomologyInjectiveModel.TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
        X U V W hW F
          (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionComplex X F)
          (CohomologyFlasqueModel.TopCat.Sheaf.injectiveResolutionAugmentation X F) n x)

end

end OAI.AlgebraicTopology.Support.CohomologyFlasqueRestrict.TopCat.Sheaf
