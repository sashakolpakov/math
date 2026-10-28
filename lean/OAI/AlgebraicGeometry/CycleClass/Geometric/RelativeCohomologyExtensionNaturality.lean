import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality

/-! # Relative Cohomology Extension Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology

noncomputable section

/-!
# Naturality and refinement independence of relative cohomology extension

The extension used here is the inverse of the actual restriction map from the
relative cochain sequence of a nested triple. Naturality is therefore obtained
by cancelling that restriction isomorphism. No extension operation is supplied
as additional data.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- A map of two nested triples restricts to a map of their inner pairs. -/
theorem relativeTripleSubspace_mapsTo {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    Set.MapsTo (LocalHomology.Cycles.subspaceMap f hA)
      (RelativeCochainTriple.Cohomology.relativeTripleSubspace X A B) (RelativeCochainTriple.Cohomology.relativeTripleSubspace Y A' B') :=
  fun _ hx => hB hx

/-- Actual relative cochain restriction commutes with pullback of triples. -/
@[reassoc]
theorem relativeCochainTripleRestriction_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M f hB ≫ RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction M X A B =
      RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction M Y A' B' ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap M (LocalHomology.Cycles.subspaceMap f hA)
          (relativeTripleSubspace_mapsTo f hA hB) := by
  unfold RelativeCochainTriple.Cohomology.relativeCochainTripleRestriction
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp M (LocalHomology.Cycles.subspaceInclusion X A) f
      (fun _ hx => hx) hB,
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp M (LocalHomology.Cycles.subspaceMap f hA)
      (LocalHomology.Cycles.subspaceInclusion Y A') (relativeTripleSubspace_mapsTo f hA hB)
      (fun _ hx => hx)]
  rfl

/-- The restriction square remains commutative on relative cohomology. -/
@[reassoc]
theorem relativeCohomologyTripleRestriction_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hB n ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M X A B n =
      RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M Y A' B' n ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceMap f hA)
          (relativeTripleSubspace_mapsTo f hA hB) n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    relativeCochainTripleRestriction_naturality M f hA hB]

/-- The canonical inverse of triple restriction is natural whenever both
restriction maps are isomorphisms by the proved adjacent vanishing groups. -/
@[reassoc]
theorem relativeCohomologyTripleExtension_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hBA : B ⊆ A) (hB'A' : B' ⊆ A')
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (n : ℕ)
    (hiX : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hjX : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1)))
    (hiY : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y A' n))
    (hjY : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y A' (n + 1))) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M Y A' B' hB'A' n hiY hjY ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hB n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceMap f hA)
          (relativeTripleSubspace_mapsTo f hA hB) n ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X A B hBA n hiX hjX := by
  let := RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso M X A B hBA n hiX hjX
  apply (cancel_mono (RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M X A B n)).1
  simp only [Category.assoc, RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension_restriction,
    Category.comp_id]
  rw [relativeCohomologyTripleRestriction_naturality M f hA hB n,
    ← Category.assoc, RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension_restriction, Category.id_comp]

/-- Forgetting relative supports is natural for actual maps of pairs. -/
@[reassoc]
theorem relativeCohomologyInclusion_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {B : Set X} {B' : Set Y}
    (hB : Set.MapsTo f B B') (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M f hB n ≫ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M Y B' n ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M f n := by
  change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n =
    HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality M f hB]

/-- Extending a class and forgetting its support commutes with pullback. -/
@[reassoc]
theorem relativeCohomologyTripleExtension_forget_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hBA : B ⊆ A) (hB'A' : B' ⊆ A')
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (n : ℕ)
    (hiX : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A n))
    (hjX : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X A (n + 1)))
    (hiY : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y A' n))
    (hjY : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M Y A' (n + 1))) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M Y A' B' hB'A' n hiY hjY ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M Y B' n ≫ AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M f n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceMap f hA)
          (relativeTripleSubspace_mapsTo f hA hB) n ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X A B hBA n hiX hjX ≫
          AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n := by
  rw [← relativeCohomologyInclusion_naturality M f hB n, ← Category.assoc,
    relativeCohomologyTripleExtension_naturality M f hBA hB'A' hA hB n
      hiX hjX hiY hjY, Category.assoc]

/-- Actual restriction of the inner pair from U to V. This applies to
arbitrary subsets, and in particular to a further open shrinking. -/
abbrev relativeCohomologyTripleShrink (M : ModuleCat.{0} R) (X : TopCat.{0})
    (U V B : Set X) (hVU : V ⊆ U) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X U B) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X V B) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (LocalHomology.Cycles.subspaceMap (𝟙 X) (fun _ hx => hVU hx))
    (relativeTripleSubspace_mapsTo (𝟙 X) (fun _ hx => hVU hx)
      (B := B) (B' := B) (fun _ hx => hx)) n

/-- Restricting to an intermediate subset and then shrinking is the direct
restriction to the smaller subset. -/
@[reassoc]
theorem relativeCohomologyTripleRestriction_shrink (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U V B : Set X) (hVU : V ⊆ U) (n : ℕ) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M X U B n ≫
        relativeCohomologyTripleShrink M X U V B hVU n =
      RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction M X V B n := by
  simpa only [relativeCohomologyTripleShrink, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id,
    Category.id_comp] using
    (relativeCohomologyTripleRestriction_naturality M (𝟙 X)
      (A := V) (B := B) (A' := U) (B' := B)
      (fun _ hx => hVU hx) (fun _ hx => hx) n).symm

/-- The existing canonical extensions agree after a further shrinking. The
proof is naturality for the identity map of the ambient pair. -/
@[reassoc]
theorem relativeCohomologyTripleExtension_shrink (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U V B : Set X) (hVU : V ⊆ U) (hBV : B ⊆ V) (n : ℕ)
    (hiU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U n))
    (hjU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U (n + 1)))
    (hiV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V n))
    (hjV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V (n + 1))) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X U B (hBV.trans hVU) n hiU hjU =
      relativeCohomologyTripleShrink M X U V B hVU n ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X V B hBV n hiV hjV := by
  simpa only [relativeCohomologyTripleShrink, AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id,
    Category.comp_id] using
    (relativeCohomologyTripleExtension_naturality M (𝟙 X)
      hBV (hBV.trans hVU) (fun _ hx => hVU hx) (fun _ hx => hx) n
      hiV hjV hiU hjU)

/-- Shrinking also preserves the resulting class after forgetting supports. -/
@[reassoc]
theorem relativeCohomologyTripleExtension_forget_shrink (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U V B : Set X) (hVU : V ⊆ U) (hBV : B ⊆ V) (n : ℕ)
    (hiU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U n))
    (hjU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U (n + 1)))
    (hiV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V n))
    (hjV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V (n + 1))) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X U B (hBV.trans hVU) n hiU hjU ≫
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n =
      relativeCohomologyTripleShrink M X U V B hVU n ≫
        RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X V B hBV n hiV hjV ≫
          AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n := by
  rw [relativeCohomologyTripleExtension_shrink M X U V B hVU hBV n
    hiU hjU hiV hjV, Category.assoc]

/-- Classes agreeing on a common refinement have equal canonical extensions.
The comparison maps are the actual inclusions of pairs. -/
theorem relativeCohomologyTripleExtension_eq_of_commonRefinement (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (U V W B : Set X) (hWU : W ⊆ U) (hWV : W ⊆ V)
    (hBW : B ⊆ W) (n : ℕ)
    (hiU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U n))
    (hjU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U (n + 1)))
    (hiV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V n))
    (hjV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V (n + 1)))
    (hiW : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X W n))
    (hjW : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X W (n + 1)))
    (cU : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X U B) n)
    (cV : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X V B) n)
    (hc : relativeCohomologyTripleShrink M X U W B hWU n cU =
      relativeCohomologyTripleShrink M X V W B hWV n cV) :
    RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X U B (hBW.trans hWU) n hiU hjU cU =
      RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X V B (hBW.trans hWV) n hiV hjV cV := by
  calc
    _ = RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X W B hBW n hiW hjW
        (relativeCohomologyTripleShrink M X U W B hWU n cU) :=
      ConcreteCategory.congr_hom
        (relativeCohomologyTripleExtension_shrink M X U W B hWU hBW n
          hiU hjU hiW hjW) cU
    _ = RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X W B hBW n hiW hjW
        (relativeCohomologyTripleShrink M X V W B hWV n cV) := congrArg _ hc
    _ = _ := (ConcreteCategory.congr_hom
      (relativeCohomologyTripleExtension_shrink M X V W B hWV hBW n
        hiV hjV hiW hjW) cV).symm

/-- Agreement on a common refinement gives the same absolute cohomology class
after canonical extension and forgetting supports. In particular, open choices
with a common open refinement yield identical classes. -/
theorem relativeCohomologyTripleExtension_forget_eq_of_commonRefinement
    (M : ModuleCat.{0} R) (X : TopCat.{0}) (U V W B : Set X)
    (hWU : W ⊆ U) (hWV : W ⊆ V) (hBW : B ⊆ W) (n : ℕ)
    (hiU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U n))
    (hjU : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X U (n + 1)))
    (hiV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V n))
    (hjV : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X V (n + 1)))
    (hiW : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X W n))
    (hjW : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X W (n + 1)))
    (cU : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of U) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X U B) n)
    (cV : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V) (RelativeCochainTriple.Cohomology.relativeTripleSubspace X V B) n)
    (hc : relativeCohomologyTripleShrink M X U W B hWU n cU =
      relativeCohomologyTripleShrink M X V W B hWV n cV) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n
        (RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X U B (hBW.trans hWU) n hiU hjU cU) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n
        (RelativeCochainTriple.Cohomology.relativeCohomologyTripleExtension M X V B (hBW.trans hWV) n hiV hjV cV) :=
  congrArg (fun c => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion M X B n c)
    (relativeCohomologyTripleExtension_eq_of_commonRefinement M X U V W B
      hWU hWV hBW n hiU hjU hiV hjV hiW hjW cU cV hc)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology
