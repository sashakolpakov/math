/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.Algebra.Homology.Notation
import OAI.AlgebraicTopology.Support.DerivedSectionsNaturality
import OAI.AlgebraicTopology.Support.DerivedSectionsExact
import OAI.CategoryTheory.Abelian.KernelCompositionShortExact
import Mathlib.Algebra.Homology.HomologySequence

/-! # Nested Localization -/

namespace OAI.AlgebraicTopology.Support.NestedLocalization.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Localization between two nested closed supports

For `V ⊆ U` open, the restrictions `F → j_{U*}F|U → j_{V*}F|V`
give a short exact sequence on injective coefficients:
`0 → Γ_{X∖U} F → Γ_{X∖V} F → ker(j_{U*}F|U → j_{V*}F|V) → 0`.
The last term is explicitly the sheaf of sections on `U` vanishing on `V`,
viewed on `X`. Thus for closed supports `S ⊆ Z`, the sequence removes `S`
from `Z`, by taking `U = X∖S` and `V = X∖Z`.

Exactness persists on every open set, since the first restriction is onto for injective (indeed
flasque) coefficients. The resulting canonical mapping-fiber comparison is the algebraic
localization step needed when extending over singular strata.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u}) {U V : Opens X} (h : V ≤ U)

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This functor sends `F` to the kernel of `j_{U*}(F|_U) → j_{V*}(F|_V)`. On an open `W`,
its sections are elements of `F(W ∩ U)` that vanish on `W ∩ V`. -/
def sheafSectionsBetweenOpens : Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := kernel ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)
  map f := kernel.map _ _ ((DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U).map f)
    ((DerivedSections.TopCat.Sheaf.openRestrictionPushforward X V).map f)
    ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).naturality f).symm
  map_id F := by
    apply (cancel_mono (kernel.ι _)).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance : (sheafSectionsBetweenOpens X h).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp [sheafSectionsBetweenOpens, Preadditive.add_comp, Preadditive.comp_add]

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. For an open `W`, this identifies sections on `W` of the kernel sheaf of restriction from
`U` to `V` with the kernel of `F(W ∩ U) → F(W ∩ V)`. -/
def sheafSectionsBetweenOpensOnOpenIso (W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsBetweenOpens X h).obj F).obj.obj (op W) ≅
      kernel (((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F).hom.app (op W)) :=
  PreservesKernel.iso (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W) ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)

@[reassoc (attr := simp)]
lemma sheafSectionsBetweenOpensOnOpenIso_hom_ι (W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsBetweenOpensOnOpenIso X h W F).hom ≫
        kernel.ι (((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F).hom.app (op W)) =
      (kernel.ι ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)).hom.app (op W) :=
  kernelComparison_comp_ι ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F) (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W)

/-- Restrict an ambient section vanishing on `V` to its section on `U`. -/
def toSheafSectionsBetweenOpens :
    DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V ⟶ sheafSectionsBetweenOpens X h where
  app F := kernel.map ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X V).app F)
    ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)
    ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F) (𝟙 _)
    (by simpa only [Category.comp_id, NatTrans.comp_app] using
      (NatTrans.congr_app (DerivedSectionsNaturality.TopCat.Sheaf.toOpenRestrictionPushforward_comp X h) F).symm)
  naturality F G f := by
    apply (cancel_mono (kernel.ι ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app G))).1
    simp only [DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside, sheafSectionsBetweenOpens, kernel.map,
      kernel.lift_ι, Category.assoc, kernel.lift_ι_assoc]
    exact congrArg
      (fun q => kernel.ι ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X V).app F) ≫ q)
      ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).naturality f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting a section supported outside `U` to `U` gives zero. -/
@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideMap_toBetween :
    DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X h ≫ toSheafSectionsBetweenOpens X h = 0 := by
  ext F : 2
  apply (cancel_mono (kernel.ι _)).1
  simp [toSheafSectionsBetweenOpens, DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap,
    DerivedSectionsOn.TopCat.Sheaf.liftSheafSectionsSupportedOutside, DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion]

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This is the sequence `Γ_{X \ U}(F) → Γ_{X \ V}(F) → ker(j_{U*}(F|_U) → j_{V*}(F|_V))`.
Its first map enlarges support and its second restricts sections to `U`. -/
def nestedSupportRestrictionShortComplex (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X h).app F)
    ((toSheafSectionsBetweenOpens X h).app F)
    (NatTrans.congr_app (sheafSectionsSupportedOutsideMap_toBetween X h) F)

/-- The support sequence is precisely the canonical sequence of three kernels. -/
lemma nestedSupportRestrictionShortComplex_eq (F : Sheaf AddCommGrpCat.{u} X) :
    nestedSupportRestrictionShortComplex X h F =
      CategoryTheory.Abelian.KernelCompositionShortExact.kernelFactorizationShortComplex
        ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F)
        ((DerivedSectionsNaturality.TopCat.Sheaf.openRestrictionPushforwardMap X h).app F)
        ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X V).app F)
        (NatTrans.congr_app (DerivedSectionsNaturality.TopCat.Sheaf.toOpenRestrictionPushforward_comp X h) F) := rfl

/-- Exactness after evaluation, by flasqueness of the terms. -/
lemma nestedSupportRestrictionSectionsShortComplex_shortExact (W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    ((nestedSupportRestrictionShortComplex X h F).map (DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W)).ShortExact := by
  rw [nestedSupportRestrictionShortComplex_eq]
  have : Epi ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W).map ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F)) :=
    DerivedSectionsLocalization.TopCat.Sheaf.toOpenRestrictionPushforward_app_epi X U F W
  exact CategoryTheory.Abelian.KernelCompositionShortExact.kernelFactorizationShortComplex_map_shortExact _ _ _ _ _

/-- The coefficientwise nested-support sequence on a complex of sheaves. -/
def nestedSupportRestrictionComplexShortComplex
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :=
  ShortComplex.mk
    (((DerivedSectionsNaturality.TopCat.Sheaf.sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex ℤᵘᵖ).app K)
    (((toSheafSectionsBetweenOpens X h).mapHomologicalComplex ℤᵘᵖ).app K)
    (by ext n; exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_toBetween X h) (K.X n))

/-- Let `V ⊆ U` and `W` be open subsets of a topological space `X`, and let `K` be an
integer-indexed complex of sheaves of abelian groups. This is the sequence of complexes obtained
degreewise from `Γ_{X \ U}(W,K) → Γ_{X \ V}(W,K) → ker(K(W ∩ U) → K(W ∩ V))`, by support
inclusion and restriction. -/
def nestedSupportRestrictionSectionsComplexShortComplex (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ) :=
  (nestedSupportRestrictionComplexShortComplex X h K).map
    ((DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation X W).mapHomologicalComplex ℤᵘᵖ)

lemma nestedSupportRestrictionSectionsComplexShortComplex_shortExact (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => nestedSupportRestrictionSectionsShortComplex_shortExact X h W (K.X n)

/-- Removing the smaller support preserves degree `n` cohomology if its two adjacent groups
vanish. Those two vanishings are hypotheses of the extension lemma. -/
lemma nestedSupportRestriction_homologyMap_isIso_of_vanishing (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    IsIso (HomologicalComplex.homologyMap
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex X h W K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact X h W K
  have : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g (hn.eq_zero_of_src _)
  have : Epi (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f (hn₁.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

end

end OAI.AlgebraicTopology.Support.NestedLocalization.TopCat.Sheaf
