/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.NestedLocalization
import OAI.AlgebraicTopology.Support.FlasqueSections
import OAI.AlgebraicTopology.Support.SectionRestrictionIs

/-! # Nested On Open -/

namespace OAI.AlgebraicTopology.Support.NestedOnOpen.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# The open-set model of the last localization term

For `V ≤ U`, global sections of the sheaf of sections on `U` vanishing on `V` are
canonically sections on `U` of the sheaf of ambient sections vanishing on `V`, both sides
being the kernel of restriction `F(U) → F(V)`. The comparison is functorial in the
coefficient sheaf, so it identifies the last complex in nested-support localization with
the supported-section complex on the complement of the smaller closed support.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u})

theorem openRestrictionImage_top (U : Opens X) :
    DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionImage X U ⊤ = U := by simp

theorem openRestrictionImage_eq_of_le {U V : Opens X} (h : V ≤ U) :
    DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionImage X V U = V := by simp_all

/-- Let `X` be a topological space and `U ⊆ X` open, with inclusion `j`. This natural isomorphism
identifies `Γ(X, j_*(F|_U))` with `F(U)` for every sheaf of abelian groups `F`. -/
def openRestrictionPushforwardTopEvaluationIso (U : Opens X) :
    DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U ⋙ DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X ⊤ ≅ DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X U :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (eqToIso (congrArg op (openRestrictionImage_top X U))))
    (fun f => (f.hom.naturality _).symm)

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This includes the kernel sheaf of `j_{U*}(F|_U) → j_{V*}(F|_V)` into `j_{U*}(F|_U)`. On
an open `W` it includes sections over `W ∩ U` vanishing on `W ∩ V` into all sections over `W ∩
U`. -/
def sheafSectionsBetweenOpensInclusion {U V : Opens X} (h : V ≤ U) :
    NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens X h ⟶ DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U where
  app F := kernel.ι ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)
  naturality F G f := by simp [NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens]

variable {U V : Opens X} (h : V ≤ U)

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This identifies global sections of `j_{V*}(F|_V)` with its sections over `U`: both
groups are `F(V)` because `V ⊆ U`. -/
def nestedSupportRestrictionTargetIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((DerivedSections.TopCat.Sheaf.openRestrictionPushforward X V).obj F).obj.obj (op ⊤) ≅
      ((DerivedSections.TopCat.Sheaf.openRestrictionPushforward X V).obj F).obj.obj (op U) :=
  F.obj.mapIso (eqToIso (congrArg op
    ((openRestrictionImage_top X V).trans (openRestrictionImage_eq_of_le X h).symm)))

/-- The comparison of the two restriction arrows is the presheaf restriction square. -/
@[reassoc]
theorem nestedSupportRestrictionTargetIso_square (F : Sheaf AddCommGrpCat.{u} X) :
    (((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F).hom.app (op ⊤)) ≫
        (nestedSupportRestrictionTargetIso X h F).hom =
      (openRestrictionPushforwardTopEvaluationIso X U).hom.app F ≫
        (((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X V).app F).hom.app (op U)) := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This identifies global sections of `ker(j_{U*}(F|_U) → j_{V*}(F|_V))` with sections over
`U` of the subsheaf of `F` supported in `X \ V`. Both are the kernel of `F(U) → F(V)`. -/
def sheafSectionsBetweenOpensGlobalIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens X h).obj F).obj.obj (op ⊤) ≅
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).obj F).obj.obj (op U) :=
  NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpensOnOpenIso X h ⊤ F ≪≫
    kernel.mapIso _ _ ((openRestrictionPushforwardTopEvaluationIso X U).app F)
      (nestedSupportRestrictionTargetIso X h F)
      (nestedSupportRestrictionTargetIso_square X h F) ≪≫
    (DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso X V U F).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison preserves the inclusion into sections on `U`. -/
@[reassoc (attr := simp)]
theorem sheafSectionsBetweenOpensGlobalIso_hom_inclusion
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) =
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
        (openRestrictionPushforwardTopEvaluationIso X U).hom.app F := by
  rw [← DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
  simp only [sheafSectionsBetweenOpensGlobalIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, kernel.mapIso_hom, kernel.map,
    kernel.lift_ι]
  rw [NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpensOnOpenIso_hom_ι_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality in the coefficient sheaf. -/
@[reassoc]
theorem sheafSectionsBetweenOpensGlobalIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (((NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
        (sheafSectionsBetweenOpensGlobalIso X h G).hom =
      (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).map f).hom.app (op U)) := by
  have : Mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U)) := by
    rw [← DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U G]
    infer_instance
  apply (cancel_mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have h₁ := congrArg (fun q => q.hom.app (op ⊤))
    ((sheafSectionsBetweenOpensInclusion X h).naturality f)
  have h₂ := congrArg (fun q => q.hom.app (op U))
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).naturality f)
  change (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).map f).hom.app (op U)) ≫
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U) =
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) ≫
      f.hom.app (op U) at h₂
  change (((NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app G).hom.app (op ⊤) =
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
      (((DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U).map f).hom.app (op ⊤)) at h₁
  rw [Category.assoc, h₂, sheafSectionsBetweenOpensGlobalIso_hom_inclusion_assoc]
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (fun q =>
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫ q)
      ((openRestrictionPushforwardTopEvaluationIso X U).hom.naturality f)

/-- Let `V ⊆ U` be open subsets of a topological space `X`. For each sheaf `F` of abelian groups,
global sections of the kernel sheaf of restriction from `U` to `V` equal sections of `F` over
`U` vanishing on `V`. This is that identification as a natural isomorphism in `F`. -/
def sheafSectionsBetweenOpensGlobalNatIso :
    NestedLocalization.TopCat.Sheaf.sheafSectionsBetweenOpens X h ⋙ DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X ⊤ ≅
      DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V ⋙ DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X U :=
  NatIso.ofComponents (sheafSectionsBetweenOpensGlobalIso X h)
    (fun f => sheafSectionsBetweenOpensGlobalIso_naturality X h f)

/-- Let `V ⊆ U` be open subsets of a topological space `X` and `K` an integer-indexed sheaf complex.
This identifies the last complex in the global sequence for supports `X \ U ⊆ X \ V` with
sections on `U` of `K` vanishing on `V`. In each degree both are the kernel of `K^q(U) →
K^q(V)`. -/
def nestedSupportRestrictionLastComplexIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (NestedLocalization.TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).X₃ ≅
      ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj
        (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).mapHomologicalComplex ℤᵘᵖ).obj K) :=
  (NatIso.mapHomologicalComplex (sheafSectionsBetweenOpensGlobalNatIso X h) ℤᵘᵖ).app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The last localization map, under the kernel comparison, is
restriction of the supported section to `U`. -/
@[reassoc]
theorem toSheafSectionsBetweenOpens_global_comparison
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((NestedLocalization.TopCat.Sheaf.toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
        (sheafSectionsBetweenOpensGlobalIso X h F).hom =
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).obj F).obj.map (homOfLE (le_top : U ≤ ⊤)).op := by
  have : Mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U)) := by
    rw [← DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
    infer_instance
  apply (cancel_mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have hι := ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  rw [hι, ← Category.assoc]
  have hg : ((NestedLocalization.TopCat.Sheaf.toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) =
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op ⊤) ≫
      ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F).hom.app (op ⊤) := by
    change (((NestedLocalization.TopCat.Sheaf.toSheafSectionsBetweenOpens X h).app F) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F)).hom.app (op ⊤) = _
    simp only [NestedLocalization.TopCat.Sheaf.toSheafSectionsBetweenOpens, sheafSectionsBetweenOpensInclusion,
      kernel.map, kernel.lift_ι]
    rfl
  rw [hg, Category.assoc]
  congr 1
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The last-complex identification retains the restriction map,
before passage to homology. -/
@[reassoc]
theorem nestedSupportRestrictionLastComplexIso_g
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (NestedLocalization.TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).g ≫
        (nestedSupportRestrictionLastComplexIso X h K).hom =
      SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction X ℤᵘᵖ
        (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V).mapHomologicalComplex ℤᵘᵖ).obj K)
        (homOfLE (le_top : U ≤ ⊤)) := by
  ext n : 1
  exact toSheafSectionsBetweenOpens_global_comparison X h (K.X n)

end

end OAI.AlgebraicTopology.Support.NestedOnOpen.TopCat.Sheaf
