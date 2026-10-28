import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections
import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportedCohomologySections
import OAI.AlgebraicTopology.Cohomology.Singular.SupportedStalk
import OAI.AlgebraicTopology.Cohomology.Singular.SheafSectionGerm

/-! # Normal Germ Compatibility -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalGermCompatibility

noncomputable section

/-!
# Relative normal classes and germs of supported cohomology sections

The open set `O` is the complement of the closed support. A local relative
class belongs to the genuine pair `(U, U ∩ O)`. Its image in the supported
cohomology sheaf is the actual relative-to-supported comparison, followed
by the canonical section comparison. This file identifies its germ with
the existing filtered-colimit comparison and transfers raw relative-germ
agreement to the precise compatibility needed for gluing normal classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

section Modules

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0}) (O : Opens X)

/-- The supported image of a raw relative germ is given by the actual
map of stalks induced by the relative section comparison. -/
@[reassoc]
theorem relativeCohomologySectionMap_germ_naturality
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n ≫
        TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hx =
      TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n) U x hx ≫
        (stalkFunctor (ModuleCat.{0} R) x).map
          (RelativeCohomologySections.Cycles.relativeCohomologySectionComparison M X O n) :=
  (stalkFunctor_map_germ U x hx (RelativeCohomologySections.Cycles.relativeCohomologySectionComparison M X O n)).symm

/-- Equality in the raw relative-cohomology stalk implies equality of
the corresponding germs in the actual supported cohomology sheaf. -/
theorem relativeCohomologySectionMap_germ_eq_of_germ_eq
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) n)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) n)
    (h : TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
        U x hxU a =
      TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
        V x hxV b) :
    TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
        U x hxU (RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n a) =
      TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
        V x hxV (RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O V n b) := by
  have h' := congrArg
    ((stalkFunctor (ModuleCat.{0} R) x).map
      (RelativeCohomologySections.Cycles.relativeCohomologySectionComparison M X O n)) h
  simpa only [stalkFunctor_map_germ_apply] using! h'

/-- On the open complement, every germ of a supported image vanishes. -/
theorem relativeCohomologySectionMap_germ_eq_zero_of_mem
    (U : Opens X) (x : X) (hx : x ∈ U) (hxO : x ∈ O) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) n) :
    TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
      U x hx (RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n a) = 0 := by
  exact @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero
    (SupportStalkVanishes.Cycles.supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem M O x hxO n)) _ _

/-- It suffices to check raw relative-germ agreement on the closed support;
the true supported stalk vanishes at every point of its open complement. -/
theorem relativeCohomologySectionMap_germ_eq_of_germ_eq_off_open
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) n)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) n)
    (h : x ∉ O →
      TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          U x hxU a =
        TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          V x hxV b) :
    TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
        U x hxU (RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n a) =
      TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
        V x hxV (RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O V n b) := by
  by_cases hxO : x ∈ O
  · rw [relativeCohomologySectionMap_germ_eq_zero_of_mem M X O U x hxU hxO n a,
      relativeCohomologySectionMap_germ_eq_zero_of_mem M X O V x hxV hxO n b]
  · exact relativeCohomologySectionMap_germ_eq_of_germ_eq M X O U V x hxU hxV n a b
      (h hxO)

/-- A family of genuine relative classes whose raw germs agree on the
closed support has compatible images in the supported cohomology sheaf. -/
theorem relativeCohomologySectionMap_compatible_of_germs_off_open
    {ι : Type*} (U : ι → Opens X) (n : ℕ)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) n)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          (U j) x hj (a j)) :
    TopCat.Presheaf.IsCompatible
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj U
      (fun i => RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O (U i) n (a i)) := by
  apply AlgebraicTopology.Cohomology.Singular.SheafGluing.moduleSheaf_compatible_of_germs
  intro i j x hi hj
  exact relativeCohomologySectionMap_germ_eq_of_germ_eq_off_open M X O
    (U i) (U j) x hi hj n (a i) (a j) (ha i j x hi hj)

/-- Raw relative-germ agreement on the support gives a unique global
supported cohomology-sheaf section, zero on the open complement. -/
theorem existsUnique_relativeCohomologySection_of_germs_off_open
    {ι : Type*} (U : ι → Opens X) (hcover : iSup U ⊔ O = ⊤) (n : ℕ)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) n)
    (ha : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), x ∉ O →
      TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          (U i) x hi (a i) =
        TopCat.Presheaf.germ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n)
          (U j) x hj (a j)) :
    ∃! s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj
        (op (⊤ : Opens X)),
      (∀ i, ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.map
          (homOfLE (le_top : U i ≤ ⊤)).op s =
        RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O (U i) n (a i)) ∧
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.map
        (homOfLE (le_top : O ≤ ⊤)).op s = 0 := by
  apply SupportedCohomologySections.Cohomology.existsUnique_supportedCohomologySection_of_germs M X O U hcover n
    (fun i => HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections M X O (U i)) n (a i))
  intro i j x hi hj
  exact relativeCohomologySectionMap_germ_eq_of_germ_eq_off_open M X O
    (U i) (U j) x hi hj n (a i) (a j) (ha i j x hi hj)

/-- The germ of the actual section comparison equals cohomology of the
actual relative-to-supported cochain germ, with the canonical stalk iso. -/
@[reassoc]
theorem relativeCohomologySectionMap_germ_cochain
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap M X O U n ≫
        TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj
          U x hx =
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm M X O U x hx) n ≫
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) x n).hom := by
  rw [RelativeCohomologySections.Cycles.relativeCohomologySectionMap_def, Category.assoc, AlgebraicTopology.Cohomology.Singular.SheafSectionGerm.sheafCohomologySectionMap_germ]
  rw [AlgebraicTopology.Cohomology.Singular.SupportedStalk.relativeToSupportedStalkGerm, HomologicalComplex.homologyMap_comp, Category.assoc]

end Modules

variable (F : Type) [Field F] [CharZero F]
  (X : TopCat.{0}) [MetrizableSpace X] (O : Opens X)

/-- Under the actual supported-stalk/relative-colimit isomorphism, the
supported image germ is exactly the original raw relative germ. -/
@[reassoc]
theorem relativeCohomologySectionMap_germ_relativeIso
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of F F) X O U n ≫
        TopCat.Presheaf.germ
          ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O).homology n).obj U x hx ≫
        (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedHomologySheafStalkRelativeIso F X O x n).hom =
      TopCat.Presheaf.germ
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of F F) X (O : Set X) n) U x hx := by
  rw [← Category.assoc, relativeCohomologySectionMap_germ_cochain]
  change (_ ≫ (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso
      (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x n).hom) ≫
    ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso
      (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O) x n).inv ≫
      (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso F X O x n).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedStalkRelativeCohomologyIso_germ F X O U x hx n

/-- The stalk map induced by the section comparison is the inverse of
the already constructed supported-stalk/relative-colimit isomorphism. -/
theorem relativeCohomologySectionComparison_stalk_eq_relativeIso_inv
    (x : X) (n : ℕ) :
    (stalkFunctor (ModuleCat.{0} F) x).map
        (RelativeCohomologySections.Cycles.relativeCohomologySectionComparison (ModuleCat.of F F) X O n) =
      (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedHomologySheafStalkRelativeIso F X O x n).inv := by
  apply (cancel_mono (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedHomologySheafStalkRelativeIso F X O x n).hom).1
  rw [Iso.inv_hom_id]
  apply stalk_hom_ext (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of F F) X (O : Set X) n)
  intro U hx
  rw [stalkFunctor_map_germ_assoc]
  simpa only [Category.comp_id] using!
    relativeCohomologySectionMap_germ_relativeIso F X O U x hx n

/-- With the proved comparison hypotheses, equality of supported image
germs is equivalent to equality of the original relative germs. -/
theorem relativeCohomologySectionMap_germ_eq_iff
    (U V : Opens X) (x : X) (hxU : x ∈ U) (hxV : x ∈ V) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) n)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of F F) (TopCat.of V)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) V) n) :
    (TopCat.Presheaf.germ
        ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O).homology n).obj
        U x hxU (RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of F F) X O U n a) =
      TopCat.Presheaf.germ
        ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of F F) X O).homology n).obj
        V x hxV (RelativeCohomologySections.Cycles.relativeCohomologySectionMap (ModuleCat.of F F) X O V n b)) ↔
      (TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of F F) X (O : Set X) n) U x hxU a =
        TopCat.Presheaf.germ
          (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of F F) X (O : Set X) n) V x hxV b) := by
  constructor
  · intro h
    have h' := congrArg (AlgebraicTopology.Cohomology.Singular.SupportedStalk.supportedHomologySheafStalkRelativeIso F X O x n).hom h
    simpa only [← ConcreteCategory.comp_apply, Category.assoc,
      relativeCohomologySectionMap_germ_relativeIso] using! h'
  · exact relativeCohomologySectionMap_germ_eq_of_germ_eq (ModuleCat.of F F)
      X O U V x hxU hxV n a b

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalGermCompatibility
