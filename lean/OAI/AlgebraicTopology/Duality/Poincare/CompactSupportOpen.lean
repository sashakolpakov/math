import OAI.AlgebraicTopology.Duality.Poincare.CompactOpenIndex
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportInsideMaps
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportExcision

/-! # Compact Support Open -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen

noncomputable section

section

/-!
# Open-subspace compact support and ambient support indices

The compact subsets of an open subspace are the ambient compact subsets
contained in that open set. Their order equivalence reindexes the actual
relative cohomology diagram. The checked fixed-support excision isomorphisms
then identify its colimit with the actual compact-support cohomology of the
open subspace. This identification respects the already constructed open
extension map into ambient compact-support cohomology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

/-- The order equivalence uses the same actual support image as fixed-support excision. -/
@[simp]
theorem openCompactsOrderIso_val (U : Opens X) (K : Compacts U) :
    (CompactOpenIndex.openCompactsOrderIso U K).val = CompactSupportExcision.openSupportImage U K := rfl

variable [T2Space X]

/-- Fixed-support excision is an isomorphism of the actual reindexed diagrams. -/
def compactSupportOpenStageDiagramIso (U : Opens X) (n : ℕ) :
    (CompactOpenIndex.openCompactsEquivalence U).functor ⋙
        CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n ≅
      CompactSupportCohomology.compactSupportCohomologyDiagram (ModuleCat.of ℚ ℚ) (TopCat.of U) n :=
  NatIso.ofComponents (fun K => CompactSupportExcision.compactSupportOpenStageIso U K n)
    (fun {_K _L} f => CompactSupportExcision.compactSupportOpenStageIso_naturality U (leOfHom f) n)

@[simp]
theorem compactSupportOpenStageDiagramIso_hom_app (U : Opens X) (n : ℕ) (K : Compacts U) :
    (compactSupportOpenStageDiagramIso U n).hom.app K =
      (CompactSupportExcision.compactSupportOpenStageIso U K n).hom := rfl

/-- Compact support cohomology of the actual open subspace is the colimit of
ambient relative cohomology over the actual compact subsets contained in it. -/
def compactSupportOpenIndexIso (U : Opens X) (n : ℕ) :
    CompactSupportInsideMaps.compactSupportedInsideCohomology (ModuleCat.of ℚ ℚ) U n ≅
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n :=
  (CompactOpenIndex.openCompactsColimitIso U (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n)).symm ≪≫
    (colim : (Compacts U ⥤ ModuleCat.{0} ℚ) ⥤ ModuleCat.{0} ℚ).mapIso
      (compactSupportOpenStageDiagramIso U n) ≪≫
        CompactSupportColimit.compactSupportCohomologyColimitIso (ModuleCat.of ℚ ℚ) (TopCat.of U) n

/-- At each actual compact support, the index comparison is exactly restriction
by fixed-support excision followed by the local compact-support insertion. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenIndexIso_ι (U : Opens X) (K : Compacts U) (n : ℕ) :
    colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n)
        (CompactOpenIndex.openCompactsOrderIso U K) ≫ (compactSupportOpenIndexIso U n).hom =
      (CompactSupportExcision.compactSupportOpenStageIso U K n).hom ≫
        CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n := by
  change colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n)
      (CompactOpenIndex.openCompactsOrderIso U K) ≫
    ((CompactOpenIndex.openCompactsColimitIso U
      (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n)).inv ≫
        colimMap (compactSupportOpenStageDiagramIso U n).hom ≫
          (CompactSupportColimit.compactSupportCohomologyColimitIso (ModuleCat.of ℚ ℚ) (TopCat.of U) n).hom) = _
  rw [CompactOpenIndex.openCompactsColimitIso_inv_ι_assoc, ι_colimMap_assoc,
    CompactSupportColimit.compactSupportCohomologyColimitIso_ι]
  rfl

/-- The inverse comparison uses the already checked inverse excision on each support. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenIndexIso_inv_ι (U : Opens X) (K : Compacts U) (n : ℕ) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n ≫
        (compactSupportOpenIndexIso U n).inv =
      (CompactSupportExcision.compactSupportOpenStageIso U K n).inv ≫
        colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n)
          (CompactOpenIndex.openCompactsOrderIso U K) := by
  apply (cancel_mono (compactSupportOpenIndexIso U n).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, compactSupportOpenIndexIso_ι, Iso.inv_hom_id_assoc]

/-- The index comparison agrees with actual open extension into ambient `Hc`. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenIndexIso_extension (U : Opens X) (n : ℕ) :
    (compactSupportOpenIndexIso U n).hom ≫ CompactSupportExcision.compactSupportOpenExtension U n =
      CompactSupportInsideMaps.compactSupportInsideToAmbient (ModuleCat.of ℚ ℚ) U n := by
  apply colimit.hom_ext
  intro A
  obtain ⟨K, rfl⟩ := (CompactOpenIndex.openCompactsOrderIso U).surjective A
  rw [compactSupportOpenIndexIso_ι_assoc, CompactSupportExcision.compactSupportCohomologyι_openExtension,
    Iso.hom_inv_id_assoc, CompactSupportInsideMaps.compactSupportInsideToAmbient_ι]
  rfl

@[reassoc (attr := simp)]
theorem compactSupportOpenIndexIso_inv_toAmbient (U : Opens X) (n : ℕ) :
    (compactSupportOpenIndexIso U n).inv ≫
        CompactSupportInsideMaps.compactSupportInsideToAmbient (ModuleCat.of ℚ ℚ) U n =
      CompactSupportExcision.compactSupportOpenExtension U n := by
  rw [← compactSupportOpenIndexIso_extension, Iso.inv_hom_id_assoc]

end

section

/-!
# Functoriality of compact-support extension through open inclusions

For nested open subspaces, the map below is the map of the genuine ambient
compact-support diagrams, transported through the proved excision
isomorphisms. It preserves each fixed compact-support class and agrees with
the already defined extension to the ambient space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} [T2Space X]

/-- The actual compact-support cohomology map of an inclusion of open subspaces. -/
def compactSupportOpenMap {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) n :=
  (compactSupportOpenIndexIso U n).inv ≫
    CompactSupportInsideMaps.compactSupportInsideMap (ModuleCat.of ℚ ℚ) h n ≫
      (compactSupportOpenIndexIso V n).hom

/-- The map commutes with the actual fixed-ambient support comparisons. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenMap_index {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    (compactSupportOpenIndexIso U n).hom ≫ compactSupportOpenMap h n =
      CompactSupportInsideMaps.compactSupportInsideMap (ModuleCat.of ℚ ℚ) h n ≫
        (compactSupportOpenIndexIso V n).hom := by
  simp [compactSupportOpenMap]

@[simp]
theorem compactSupportOpenMap_id (U : Opens X) (n : ℕ) :
    compactSupportOpenMap (le_refl U) n = 𝟙 _ := by
  simp [compactSupportOpenMap]

@[reassoc (attr := simp)]
theorem compactSupportOpenMap_comp {U V W : Opens X}
    (h : U ≤ V) (h' : V ≤ W) (n : ℕ) :
    compactSupportOpenMap h n ≫ compactSupportOpenMap h' n =
      compactSupportOpenMap (h.trans h') n := by
  simp [compactSupportOpenMap, Category.assoc]

/-- Extension through an intermediate open subspace agrees with direct ambient extension. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenMap_extension {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    compactSupportOpenMap h n ≫ CompactSupportExcision.compactSupportOpenExtension V n =
      CompactSupportExcision.compactSupportOpenExtension U n := by
  simp only [compactSupportOpenMap, Category.assoc,
    compactSupportOpenIndexIso_extension, CompactSupportInsideMaps.compactSupportInsideMap_toAmbient]
  rw [← compactSupportOpenIndexIso_extension U n]
  simp

/-- A fixed ambient compact support contained in `U` supplies a class in `Hc(U)`. -/
def compactSupportOpenStageClass (U : Opens X) (K : U.compactsInside) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K.val : Set X)ᶜ n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n :=
  colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n) K ≫
    (compactSupportOpenIndexIso U n).hom

/-- This class is precisely the restriction by excision followed by the local stage insertion. -/
theorem compactSupportOpenStageClass_of_local (U : Opens X) (K : Compacts U) (n : ℕ) :
    compactSupportOpenStageClass U (CompactOpenIndex.openCompactsOrderIso U K) n =
      (CompactSupportExcision.compactSupportOpenStageIso U K n).hom ≫
        CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K n :=
  compactSupportOpenIndexIso_ι U K n

/-- The class of a fixed compact support is preserved by enlargement of the open neighborhood. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenStageClass_map {U V : Opens X} (h : U ≤ V)
    (K : U.compactsInside) (n : ℕ) :
    compactSupportOpenStageClass U K n ≫ compactSupportOpenMap h n =
      compactSupportOpenStageClass V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) n := by
  simp [compactSupportOpenStageClass, Category.assoc]

/-- Ambient extension of a fixed compact-stage class is its original ambient stage insertion. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenStageClass_extension (U : Opens X) (K : U.compactsInside)
    (n : ℕ) :
    compactSupportOpenStageClass U K n ≫ CompactSupportExcision.compactSupportOpenExtension U n =
      CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) X K.val n := by
  simp [compactSupportOpenStageClass, Category.assoc, compactSupportOpenIndexIso_extension]

/-- Maps out of local compact-support cohomology are determined by the ambient compact stages. -/
theorem compactSupportOpenStageClass_hom_ext (U : Opens X) (n : ℕ)
    {M : ModuleCat.{0} ℚ}
    {f g : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⟶ M}
    (h : ∀ K : U.compactsInside,
      compactSupportOpenStageClass U K n ≫ f = compactSupportOpenStageClass U K n ≫ g) :
    f = g := by
  apply (cancel_epi (compactSupportOpenIndexIso U n).hom).1
  apply colimit.hom_ext
  intro K
  simpa only [compactSupportOpenStageClass, Category.assoc] using h K

/-- Preservation of every genuine compact stage uniquely determines the open inclusion map. -/
theorem compactSupportOpenMap_unique {U V : Opens X} (h : U ≤ V) (n : ℕ)
    (f : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) n)
    (hf : ∀ K : U.compactsInside,
      compactSupportOpenStageClass U K n ≫ f =
        compactSupportOpenStageClass V ((CompactSupportInsideMaps.compactsInsideMap h).obj K) n) :
    f = compactSupportOpenMap h n := by
  apply compactSupportOpenStageClass_hom_ext U n
  intro K
  rw [hf, compactSupportOpenStageClass_map]

/-- The genuine covariant compact-support cohomology functor on the open subsets of a space. -/
def compactSupportOpenCohomologyFunctor (X : TopCat.{0}) [T2Space X] (n : ℕ) :
    Opens X ⥤ ModuleCat.{0} ℚ where
  obj U := CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n
  map f := compactSupportOpenMap (leOfHom f) n
  map_id U := compactSupportOpenMap_id U n
  map_comp f g := (compactSupportOpenMap_comp (leOfHom f) (leOfHom g) n).symm

@[simp]
theorem compactSupportOpenCohomologyFunctor_map (n : ℕ) {U V : Opens X} (h : U ≤ V) :
    (compactSupportOpenCohomologyFunctor X n).map (homOfLE h) =
      compactSupportOpenMap h n := rfl

/-- Actual extension into the ambient space is natural for the open-subset functor. -/
def compactSupportOpenExtensionNat (X : TopCat.{0}) [T2Space X] (n : ℕ) :
    compactSupportOpenCohomologyFunctor X n ⟶
      (Functor.const (Opens X)).obj
        (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) where
  app U := CompactSupportExcision.compactSupportOpenExtension U n
  naturality U V f := by
    change compactSupportOpenMap (leOfHom f) n ≫ CompactSupportExcision.compactSupportOpenExtension V n =
      CompactSupportExcision.compactSupportOpenExtension U n ≫ 𝟙 _
    rw [compactSupportOpenMap_extension, Category.comp_id]

end

/-!
# The actual preimage-support formula for an open-stage class

An ambient compact support contained in an open subset restricts to its
actual compact preimage in that open subset. The associated relative cochain
map is literal pullback along the inclusion. The existing open-stage class
is its induced cohomology map followed by the local compact-support insertion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}}

/-- The preimage of a compact support inside an open set has the original support as its image. -/
@[simp]
theorem openSupportImage_openCompactPreimage (U : Opens X) (K : U.compactsInside) :
    CompactSupportExcision.openSupportImage U (CompactOpenIndex.openCompactPreimage U K) = K.val := by
  exact congrArg Subtype.val ((CompactOpenIndex.openCompactsOrderIso U).apply_symm_apply K)

/-- Literal relative cochain pullback to the compact preimage in an open subset. -/
def compactSupportOpenPreimageCochainRestriction (U : Opens X) (K : U.compactsInside) :
    CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) X K.val ⟶
      CompactSupportCohomology.compactSupportCochainStage (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (CompactOpenIndex.openCompactPreimage U K) :=
  Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) U.inclusion' (fun _ hx => hx)

/-- The relative map restricts its underlying ordinary cochain along the actual inclusion. -/
@[reassoc (attr := simp)]
theorem compactSupportOpenPreimageCochainRestriction_inclusion
    (U : Opens X) (K : U.compactsInside) :
    compactSupportOpenPreimageCochainRestriction U K ≫
        CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
          (CompactOpenIndex.openCompactPreimage U K) =
      CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) X K.val ≫
        Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) U.inclusion' :=
  Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality (ModuleCat.of ℚ ℚ) U.inclusion' (fun _ hx => hx)

/-- The induced map is the homology map of the actual relative cochain restriction. -/
abbrev compactSupportOpenPreimageCohomologyRestriction
    (U : Opens X) (K : U.compactsInside) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (K.val : Set X)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
        (CompactOpenIndex.openCompactPreimage U K : Set U)ᶜ n :=
  HomologicalComplex.homologyMap (compactSupportOpenPreimageCochainRestriction U K) n

/-- Support-image bookkeeping agrees with literal restriction, as seen in the actual kernels. -/
private theorem preimageRestriction_factorization (U : Opens X) (K : U.compactsInside)
    (h : K.val ≤ CompactSupportExcision.openSupportImage U (CompactOpenIndex.openCompactPreimage U K)) :
    CompactSupportCohomology.compactSupportCochainMap (ModuleCat.of ℚ ℚ) h ≫
        CompactSupportExcision.compactSupportOpenStageRestriction U (CompactOpenIndex.openCompactPreimage U K) =
      compactSupportOpenPreimageCochainRestriction U K := by
  apply (cancel_mono
    (CompactSupportCohomology.compactSupportCochainStageInclusion (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (CompactOpenIndex.openCompactPreimage U K))).1
  rw [Category.assoc, CompactSupportExcision.compactSupportOpenStageRestriction_inclusion,
    CompactSupportCohomology.compactSupportCochainMap_inclusion_assoc,
    compactSupportOpenPreimageCochainRestriction_inclusion]

/-- The genuine preimage-support restriction is a quasi-isomorphism by open excision. -/
theorem compactSupportOpenPreimageCochainRestriction_quasiIso [T2Space X]
    (U : Opens X) (K : U.compactsInside) :
    QuasiIso (compactSupportOpenPreimageCochainRestriction U K) := by
  exact CompactSupportExcision.compactSupportExcisionCochainMap_quasiIso X (U : Set X) (K.val : Set X)
    K.val.isCompact U.isOpen K.property

/-- The open-stage class is literal relative restriction followed by local support insertion. -/
theorem compactSupportOpenStageClass_preimage [T2Space X]
    (U : Opens X) (K : U.compactsInside) (n : ℕ) :
    compactSupportOpenStageClass U K n =
      HomologicalComplex.homologyMap (compactSupportOpenPreimageCochainRestriction U K) n ≫
        CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U)
          (CompactOpenIndex.openCompactPreimage U K) n := by
  have h : K ≤ CompactOpenIndex.openCompactsOrderIso U (CompactOpenIndex.openCompactPreimage U K) :=
    le_of_eq ((CompactOpenIndex.openCompactsOrderIso U).apply_symm_apply K).symm
  have hval : K.val ≤ CompactSupportExcision.openSupportImage U (CompactOpenIndex.openCompactPreimage U K) := h
  have hclass :
      CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) hval n ≫
          compactSupportOpenStageClass U (CompactOpenIndex.openCompactsOrderIso U (CompactOpenIndex.openCompactPreimage U K)) n =
        compactSupportOpenStageClass U K n := by
    exact colimit.w_assoc
      (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) U n) (homOfLE h)
      (compactSupportOpenIndexIso U n).hom
  rw [← hclass, compactSupportOpenStageClass_of_local,
    CompactSupportExcision.compactSupportOpenStageIso_hom, ← Category.assoc]
  change (HomologicalComplex.homologyMap
      (CompactSupportCohomology.compactSupportCochainMap (ModuleCat.of ℚ ℚ) hval) n ≫
      HomologicalComplex.homologyMap
        (CompactSupportExcision.compactSupportOpenStageRestriction U (CompactOpenIndex.openCompactPreimage U K)) n) ≫ _ = _
  rw [← HomologicalComplex.homologyMap_comp, preimageRestriction_factorization]

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen
