/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.DerivedSectionsNaturality
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-! # Flasque Sections -/

namespace OAI.AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Supported sections preserve flasqueness

A supported section over `V` glues with zero on the excluded open `U` to a section on
`V ⊔ U`. Flasqueness extends that section to `W ⊔ U` when `V ≤ W`, and its restriction to
`W` vanishes on `W ⊓ U`, so it lies in the kernel defining supported sections.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u}) (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X)

/-- The preceding identification preserves the restriction morphism. -/
@[reassoc]
theorem toOpenRestrictionPushforward_intersection :
    (((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F).hom.app (op V)) ≫
      (DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso X U V F).hom =
        F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The supported-section inclusion restricts to zero on the intersection. -/
@[reassoc]
theorem supportedOutsideInclusion_restrict_intersection :
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
      F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op = 0 := by
  rw [← toOpenRestrictionPushforward_intersection X U V F, ← Category.assoc]
  have h := congrArg (fun f => f.hom.app (op V))
    (DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion_restriction X U F)
  change ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) ≫
    ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F).hom.app (op V) = 0 at h
  rw [h, zero_comp]

/-- A section zero on the intersection lifts into the supported-section kernel, along the
canonical on-open kernel comparison. -/
theorem exists_supportedOutsideSection_of_restrict_eq_zero
    (s : F.presheaf.obj (op V))
    (hs : F.obj.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op s = 0) :
    ∃ t : ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).presheaf.obj (op V),
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) t = s := by
  let r := ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have hr : r s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (DerivedSections.TopCat.Sheaf.supportedOutsideIntersectionIso X U V F).hom).1
    rw [map_zero]
    exact (ConcreteCategory.congr_hom
      (toOpenRestrictionPushforward_intersection X U V F) s).trans hs
  let e := DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso X U V F ≪≫ AddCommGrpCat.kernelIsoKer r
  let a : r.hom.ker := ⟨s, hr⟩
  refine ⟨e.inv a, ?_⟩
  have he : e.hom ≫ AddCommGrpCat.ofHom r.hom.ker.subtype =
      ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) := by
    simp only [e, Iso.trans_hom, Category.assoc,
      AddCommGrpCat.kernelIsoKer_hom_comp_subtype]
    exact DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F
  rw [← he]
  change (AddCommGrpCat.ofHom r.hom.ker.subtype) (e.hom (e.inv a)) = s
  have hai : e.hom (e.inv a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
  rw [hai]
  rfl

/-- Let `X` be a topological space, `U,V` open, and `F` a sheaf of abelian groups. A section of `F`
on `V` vanishing on `V ∩ U` glues uniquely to the zero section on `U`. This additive map sends
it to the resulting section on `V ∪ U`. -/
def supportedOutsideGlueZero :
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op (V ⊔ U)) :=
  F.interUnionPullbackConeLift V U
    (PullbackCone.mk
      (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
      (0 : ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ⟶ F.obj.obj (op U))
      (by rw [supportedOutsideInclusion_restrict_intersection, zero_comp]))

/-- Gluing with zero preserves the given section on its original open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_left :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op =
        ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) :=
  F.interUnionPullbackConeLift_left V U _

/-- The same glued section is exactly zero on the excluded open. -/
@[reassoc (attr := simp)]
theorem supportedOutsideGlueZero_restrict_right :
    supportedOutsideGlueZero X U V F ≫
      F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op = 0 :=
  F.interUnionPullbackConeLift_right V U _

variable {V} {W : Opens X}

/-- Every supported section extends along an open inclusion when the original sheaf
is flasque. The extension is produced by gluing with zero before extending. -/
theorem sheafSectionsSupportedOutside_restriction_surjective [F.IsFlasque]
    (hVW : V ≤ W) :
    Function.Surjective (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).obj.map
      (homOfLE hVW).op) := by
  intro a
  let G := (DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F
  let ι := (DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F
  have hsup : V ⊔ U ≤ W ⊔ U := sup_le_sup_right hVW U
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective
    (F.obj.map (homOfLE hsup).op)).mp inferInstance
      (supportedOutsideGlueZero X U V F a)
  have htU : F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t = 0 := by
    calc
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (F.obj.map (homOfLE hsup).op t) := by
        rw [← Functor.map_comp_apply]
        rfl
      _ = F.obj.map (homOfLE (le_sup_right : U ≤ V ⊔ U)).op
          (supportedOutsideGlueZero X U V F a) := by rw [ht]
      _ = 0 := ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_right X U V F) a
  let b := F.obj.map (homOfLE (le_sup_left : W ≤ W ⊔ U)).op t
  have hb : F.obj.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op b = 0 := by
    calc
      _ = F.obj.map (homOfLE (inf_le_right : W ⊓ U ≤ U)).op
          (F.obj.map (homOfLE (le_sup_right : U ≤ W ⊔ U)).op t) := by
        dsimp [b]
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl
      _ = 0 := by rw [htU, map_zero]
  obtain ⟨c, hc⟩ := exists_supportedOutsideSection_of_restrict_eq_zero X U W F b hb
  have hι : Function.Injective (ι.hom.app (op V)) := by
    apply (AddCommGrpCat.mono_iff_injective _).mp
    change Mono (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V))
    rw [← DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso_hom_ι X U V F]
    infer_instance
  refine ⟨c, hι ?_⟩
  calc
    ι.hom.app (op V) (G.obj.map (homOfLE hVW).op c) =
        F.obj.map (homOfLE hVW).op (ι.hom.app (op W) c) :=
      ConcreteCategory.congr_hom (ι.hom.naturality (homOfLE hVW).op) c
    _ = F.obj.map (homOfLE hVW).op b := by rw [hc]
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (F.obj.map (homOfLE hsup).op t) := by
      dsimp [b]
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      rfl
    _ = F.obj.map (homOfLE (le_sup_left : V ≤ V ⊔ U)).op
        (supportedOutsideGlueZero X U V F a) := by rw [ht]
    _ = ι.hom.app (op V) a :=
      ConcreteCategory.congr_hom (supportedOutsideGlueZero_restrict_left X U V F) a

/-- The sheaf-valued supported-sections functor preserves flasque sheaves. -/
instance sheafSectionsSupportedOutside_isFlasque [F.IsFlasque] :
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).IsFlasque where
  epi {V W} i := by
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (sheafSectionsSupportedOutside_restriction_surjective X U F (leOfHom i.unop))

/-- Equivalently, sections supported in any closed subset preserve flasqueness. -/
instance sheafSectionsWithClosedSupport_isFlasque (Z : Closeds X) [F.IsFlasque] :
    ((DerivedSectionsOn.TopCat.Sheaf.sheafSectionsWithClosedSupport X Z).obj F).IsFlasque :=
  sheafSectionsSupportedOutside_isFlasque X Z.compl F

end

end OAI.AlgebraicTopology.Support.FlasqueSections.TopCat.Sheaf
