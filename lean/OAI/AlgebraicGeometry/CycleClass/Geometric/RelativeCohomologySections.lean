import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality

/-! # Relative Cohomology Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections

noncomputable section

/-!
# Relative cohomology and actual supported cohomology-sheaf sections

The maps below are the composite of the actual relative-to-supported cochain
comparison and the canonical section-to-cohomology-sheaf map. The top-open
identification is included explicitly, so global classes belong to the
ordinary relative singular cohomology of the original pair.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality
open _root_.TopCat.Presheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {R : Type} [Ring R] (M : ModuleCat.{0} R) (X : TopCat.{0})

/-- Restrict a genuine global relative class along the actual open inclusion. -/
def relativeCohomologyOpenRestriction (A : Set X) (U : Opens X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace A U) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceInclusion X (U : Set X))
    (fun _ hx => hx) n

/-- Passing through the top-open homeomorphism gives exactly the actual
restriction of the original pair, including its coefficient normalization. -/
theorem relativeCohomologyOpenRestriction_eq (A : Set X) (U : Opens X) (n : ℕ) :
    relativeCohomologyOpenRestriction M X A U n =
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso M X A n).inv ≫
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X A n).map
          (homOfLE (le_top : U ≤ ⊤)).op := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceInclusion X (U : Set X))
      (fun _ hx => hx) n =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (Opens.inclusionTopIso X).hom
        (fun _ hx => hx) n ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M
        ((Opens.toTopCat X).map (homOfLE (le_top : U ≤ ⊤))) (fun _ hx => hx) n
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

variable (O : Opens X)

/-- The genuine relative-cohomology presheaf maps to the actual homology
sheaf of the supported singular cochain complex. -/
def relativeCohomologySectionComparison (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n ⟶
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj :=
  AlgebraicTopology.Cohomology.Singular.RelativeSupportedNaturality.relativeToSupportedCohomologyPresheafMap M X O n ≫
    AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionComparison (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) n

/-- The actual comparison on a specified open subset. -/
abbrev relativeCohomologySectionMap (U : Opens X) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) U) n ⟶
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj (op U) :=
  (relativeCohomologySectionComparison M X O n).app (op U)

/-- The local section map is induced by the true relative cochain map,
followed by the canonical map to the cohomology sheaf. -/
theorem relativeCohomologySectionMap_def (U : Opens X) (n : ℕ) :
    relativeCohomologySectionMap M X O U n =
      HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.SupportedRelativeMap.relativeToSupportedSheafSections M X O U) n ≫
        AlgebraicTopology.Cohomology.Singular.SheafSections.sheafCohomologySectionMap (SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O) U n := rfl

@[reassoc]
theorem relativeCohomologySectionMap_naturality {U V : Opens X} (i : U ⟶ V) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf M X (O : Set X) n).map i.op ≫
        relativeCohomologySectionMap M X O U n =
      relativeCohomologySectionMap M X O V n ≫
        ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.map i.op :=
  (relativeCohomologySectionComparison M X O n).naturality i.op

/-- The global comparison starts from the original relative singular
cohomology group, rather than from the homeomorphic top-open subtype. -/
def relativeCohomologyGlobalSectionMap (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (O : Set X) n ⟶
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj (op (⊤ : Opens X)) :=
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso M X (O : Set X) n).inv ≫
    relativeCohomologySectionMap M X O ⊤ n

/-- The global comparison commutes with actual relative restriction and
with the actual restriction of the supported cohomology sheaf. -/
@[reassoc]
theorem relativeCohomologyGlobalSectionMap_restrict (U : Opens X) (n : ℕ) :
    relativeCohomologyGlobalSectionMap M X O n ≫
        ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.map
          (homOfLE (le_top : U ≤ ⊤)).op =
      relativeCohomologyOpenRestriction M X (O : Set X) U n ≫
        relativeCohomologySectionMap M X O U n := by
  rw [relativeCohomologyOpenRestriction_eq, relativeCohomologyGlobalSectionMap]
  simp only [Category.assoc]
  rw [relativeCohomologySectionMap_naturality]

/-- Taking the germ of the global image is the same as first restricting
the original relative class to any actual neighborhood. -/
@[reassoc]
theorem relativeCohomologyGlobalSectionMap_germ
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    relativeCohomologyGlobalSectionMap M X O n ≫
        TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj ⊤ x
          (show x ∈ (⊤ : Opens X) from trivial) =
      relativeCohomologyOpenRestriction M X (O : Set X) U n ≫
        relativeCohomologySectionMap M X O U n ≫
          TopCat.Presheaf.germ ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj U x hx := by
  rw [← relativeCohomologyGlobalSectionMap_restrict_assoc]
  rw [TopCat.Presheaf.germ_res]

/-- Compatible images of actual local relative classes glue uniquely in
the genuine supported cohomology sheaf. No descent property of the raw
cohomology presheaf is used. -/
theorem existsUnique_relativeCohomologyGlobalSection
    {ι : Type*} (U : ι → Opens X) (hU : iSup U = ⊤) (n : ℕ)
    (a : ∀ i, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of (U i))
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (O : Set X) (U i)) n)
    (ha : TopCat.Presheaf.IsCompatible
      ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj U
      (fun i => relativeCohomologySectionMap M X O (U i) n (a i))) :
    ∃! s : ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.obj
        (op (⊤ : Opens X)),
      ∀ i, ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).obj.map
          (homOfLE (le_top : U i ≤ ⊤)).op s =
        relativeCohomologySectionMap M X O (U i) n (a i) :=
  ((SupportStalkVanishes.Cohomology.supportedSingularSheafComplex M X O).homology n).existsUnique_gluing' U ⊤
    (fun i => homOfLE (le_top : U i ≤ ⊤)) (by rw [hU]) _ ha

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologySections
