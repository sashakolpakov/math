/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.DerivedSectionsShift
import OAI.Algebra.Homology.FunctorPlusShiftNaturality

/-! # Derived Sections Naturality -/

namespace OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Naturality of derived sections with closed support

Support enlargement comes from the kernel inclusion, and is then derived by
the universal property. In particular, forgetting support is the map to whole-space support.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u})

/-- The support-forgetting inclusion is the kernel monomorphism. -/
instance sheafSectionsSupportedOutsideInclusion_mono (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F) :=
  inferInstanceAs (Mono (kernel.ι ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F)))

/-- The ambient open used when restricting to `U` and pushing forward again. -/
abbrev openRestrictionImage (U W : Opens X) : Opens X :=
  U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj W)

theorem openRestrictionImage_mono {U V : Opens X} (h : V ≤ U) (W : Opens X) :
    openRestrictionImage X V W ≤ openRestrictionImage X U W := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨⟨y.1, h y.2⟩, hy, rfl⟩

/-- Let `V ⊆ U` be open subsets of a topological space `X`. This natural map from direct image of
restriction to `U` to direct image of restriction to `V` acts on a sheaf `F` and open `W` by
`F(W ∩ U) → F(W ∩ V)`. -/
def openRestrictionPushforwardMap {U V : Opens X} (h : V ≤ U) :
    DerivedSections.TopCat.Sheaf.openRestrictionPushforward X U ⟶ DerivedSections.TopCat.Sheaf.openRestrictionPushforward X V where
  app F := ⟨{
    app W := F.obj.map (homOfLE (openRestrictionImage_mono X h W.unop)).op
    naturality W W' f := by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    ext W : 2
    exact (f.hom.naturality _).symm

/-- Further restriction agrees with direct restriction from the ambient sheaf. -/
@[reassoc (attr := simp)]
theorem toOpenRestrictionPushforward_comp {U V : Opens X} (h : V ≤ U) :
    DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U ≫ openRestrictionPushforwardMap X h =
      DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X V := by
  ext F : 2
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  ext W : 2
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The canonical inclusion of sections supported outside `U` into those supported
outside the smaller open `V`. -/
def sheafSectionsSupportedOutsideMap {U V : Opens X} (h : V ≤ U) :
    DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U ⟶ DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X V where
  app F := DerivedSectionsOn.TopCat.Sheaf.liftSheafSectionsSupportedOutside X V
    ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F) (by
      rw [← NatTrans.congr_app (toOpenRestrictionPushforward_comp X h) F]
      simp only [NatTrans.comp_app, ← Category.assoc,
        DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion_restriction, zero_comp])
  naturality F G f := by
    apply (cancel_mono ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).app G)).1
    simp only [Category.assoc, DerivedSectionsOn.TopCat.Sheaf.liftSheafSectionsSupportedOutside_inclusion]
    rw [(DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V).naturality f,
      ← Category.assoc, DerivedSectionsOn.TopCat.Sheaf.liftSheafSectionsSupportedOutside_inclusion]
    exact (DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).naturality f

/-- Support enlargement preserves the inclusion into the coefficient sheaf. -/
@[reassoc (attr := simp)]
theorem sheafSectionsSupportedOutsideMap_inclusion {U V : Opens X} (h : V ≤ U) :
    sheafSectionsSupportedOutsideMap X h ≫ DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X V =
      DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U := by
  ext F
  exact DerivedSectionsOn.TopCat.Sheaf.liftSheafSectionsSupportedOutside_inclusion X V _ _

@[simp]
theorem sheafSectionsSupportedOutsideMap_refl (U : Opens X) :
    sheafSectionsSupportedOutsideMap X (le_refl U) = 𝟙 (DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U) := by
  ext F
  apply (cancel_mono ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X U).app F)).1
  simp [sheafSectionsSupportedOutsideMap]

@[reassoc (attr := simp)]
theorem sheafSectionsSupportedOutsideMap_comp {U V W : Opens X}
    (h : V ≤ U) (h' : W ≤ V) :
    sheafSectionsSupportedOutsideMap X h ≫ sheafSectionsSupportedOutsideMap X h' =
      sheafSectionsSupportedOutsideMap X (h'.trans h) := by
  ext F
  apply (cancel_mono ((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X W).app F)).1
  simp [sheafSectionsSupportedOutsideMap]

/-- The coefficient-level support-enlargement map for closed subsets. -/
def sheafSectionsWithClosedSupportMap {Z W : Closeds X} (h : Z ≤ W) :
    DerivedSectionsOn.TopCat.Sheaf.sheafSectionsWithClosedSupport X Z ⟶ DerivedSectionsOn.TopCat.Sheaf.sheafSectionsWithClosedSupport X W :=
  sheafSectionsSupportedOutsideMap X (show W.compl ≤ Z.compl from fun _ hx hz ↦ hx (h hz))

/-- Let `Z ⊆ W` be closed subsets of a topological space `X`. This natural transformation includes
the group of global sections of a sheaf of abelian groups supported in `Z` into the group of
those supported in `W`. -/
def closedSupportSectionsMap {Z W : Closeds X} (h : Z ≤ W) :
    DerivedSectionsOn.TopCat.Sheaf.closedSupportSections X Z ⟶ DerivedSectionsOn.TopCat.Sheaf.closedSupportSections X W :=
  Functor.whiskerRight (sheafSectionsWithClosedSupportMap X h)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op ⊤))

@[simp]
theorem closedSupportSectionsMap_refl (Z : Closeds X) :
    DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap X (le_refl Z) = 𝟙 (DerivedSectionsOn.TopCat.Sheaf.closedSupportSections X Z) := by
  simp [DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap, sheafSectionsWithClosedSupportMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem closedSupportSectionsMap_comp {Z W T : Closeds X} (h : Z ≤ W) (h' : W ≤ T) :
    DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap X h ≫ DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap X h' =
      DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap X (h.trans h') := by
  simp [DerivedSectionsNaturality.TopCat.Sheaf.closedSupportSectionsMap, sheafSectionsWithClosedSupportMap,
    ← Functor.whiskerRight_comp]

local instance derivedSupportNaturalitySheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance derivedSupportNaturalityGroupDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

/-- Let `Z ⊆ W` be closed subsets of a topological space `X`. This natural map `RΓ_Z(X,-) →
RΓ_W(X,-)` on bounded-below sheaf complexes is obtained by applying inclusion of supported
global sections to an injective resolution. -/
def derivedClosedSupportSectionsMap {Z W : Closeds X} (h : Z ≤ W) :
    DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections X Z ⟶ DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections X W :=
  (Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus (closedSupportSectionsMap X h))

/-- The support-enlargement maps commute with the coherent shifts. -/
instance derivedClosedSupportSectionsMap_commShift {Z W : Closeds X} (h : Z ≤ W) :
    NatTrans.CommShift (derivedClosedSupportSectionsMap X h) ℤ :=
  inferInstanceAs (NatTrans.CommShift (Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus (closedSupportSectionsMap X h)) ℤ)

@[simp]
theorem derivedClosedSupportSectionsMap_refl (Z : Closeds X) :
    derivedClosedSupportSectionsMap X (le_refl Z) =
      𝟙 (DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections X Z) := by
  simp [derivedClosedSupportSectionsMap, DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSections]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem derivedClosedSupportSectionsMap_comp {Z W T : Closeds X}
    (h : Z ≤ W) (h' : W ≤ T) :
    derivedClosedSupportSectionsMap X h ≫ derivedClosedSupportSectionsMap X h' =
      derivedClosedSupportSectionsMap X (h.trans h') := by
  simp [derivedClosedSupportSectionsMap, ← Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_comp]

/-- The derived-unit square identifies the support map on injective resolutions. -/
@[reassoc (attr := simp)]
theorem derivedClosedSupportSectionsMap_unit_app {Z W : Closeds X} (h : Z ≤ W)
    (K : HomotopyCategory.Plus (Sheaf AddCommGrpCat.{u} X)) :
    (DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSectionsUnit X Z).app K ≫
        (derivedClosedSupportSectionsMap X h).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.mapHomotopyCategoryPlus (closedSupportSectionsMap X h)).app K) ≫
        (DerivedSectionsOn.TopCat.Sheaf.derivedClosedSupportSectionsUnit X W).app K :=
  (Algebra.Homology.DerivedFunctorPlusNaturality.CategoryTheory.NatTrans.rightDerivedFunctorPlus_unit_app (closedSupportSectionsMap X h)) K

end

end OAI.AlgebraicTopology.Support.DerivedSectionsNaturality.TopCat.Sheaf
