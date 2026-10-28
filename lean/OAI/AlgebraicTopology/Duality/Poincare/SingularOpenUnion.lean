import OAI.Topology.Euclidean.IncreasingCover
import OAI.Topology.Euclidean.FilteredCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.IncreasingCochains
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Singular Open Union -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SingularOpenUnion

noncomputable section

/-!
# Ordinary singular chains on increasing open unions

The actual integral singular chain complex of an increasing open cover is
the colimit of the actual chain complexes of its members. Every finite chain
comes from one member, by compactness of its finitely many simplex images.
The degreewise colimit universal property and exactness of filtered module
colimits then give the canonical comparison on ordinary singular homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles OAI.AlgebraicTopology.Cohomology.Singular.IncreasingCochains
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

/-- The genuine chain map of an open-subspace inclusion. -/
abbrev singularOpenChainInclusion (V : Opens X) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of V) ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X :=
  AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map V.inclusion'

/-- Its degree map has exactly the usual finite-coefficient pushforward. -/
theorem singularOpenChainInclusion_coefficients (V : Opens X) (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of V)).X n) :
    AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainCoefficients X n ((singularOpenChainInclusion V).f n c) =
      Finsupp.mapDomain ((TopCat.toSSet.map V.inclusion').app (.op ⦋n⦌))
        (AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainCoefficients (TopCat.of V) n c) :=
  AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles.subspaceChainInclusion_coefficients X (V : Set X) n c

/-- An actual open inclusion is injective in every singular chain degree. -/
theorem singularOpenChainInclusion_injective (V : Opens X) (n : ℕ) :
    Function.Injective ((singularOpenChainInclusion V).f n) := by
  change Function.Injective ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (V : Set X)).f n)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

variable (U : ℕ → Opens X) (hmono : Monotone U)

/-- The actual increasing diagram of ordinary singular chain complexes. -/
def increasingOpenChainDiagram : ℕ ⥤ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  hmono.functor ⋙ Opens.toTopCat X ⋙ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor

@[simp]
theorem increasingOpenChainDiagram_obj (i : ℕ) :
    (increasingOpenChainDiagram U hmono).obj i =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i)) := rfl

@[simp]
theorem increasingOpenChainDiagram_map {i j : ℕ} (hij : i ≤ j) :
    (increasingOpenChainDiagram U hmono).map (homOfLE hij) =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (Cohomology.Singular.IncreasingCochains.increasingOpenInclusion U hmono hij) := rfl

/-- The cocone whose legs are the original inclusion chain maps. -/
def increasingOpenChainCocone : Cocone (increasingOpenChainDiagram U hmono) where
  pt := AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X
  ι :=
    { app i := singularOpenChainInclusion (U i)
      naturality i j f := by
        change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
            ((Opens.toTopCat X).map (hmono.functor.map f)) ≫
            AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (U j).inclusion' =
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (U i).inclusion' ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        congr 1 }

section FullCover

variable (hcover : (⨆ i, U i) = ⊤)

include hmono hcover

/-- Every actual finite singular chain has an actual preimage in a single
open stage. Compact simplex images and finite support prove the assertion. -/
theorem exists_increasingOpenChain_lift (n : ℕ) (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ i, ∃ b : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i))).X n,
      (singularOpenChainInclusion (U i)).f n b = c := by
  classical
  obtain ⟨i, hi⟩ := Topology.Euclidean.IncreasingCover.Globalization.exists_finset_singularSimplex_ranges_subset U hmono hcover
    (AlgebraicGeometry.CycleClass.Geometric.SingularChainSupport.Cycles.singularChainSupport c)
  have hc : c ∈ LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X (U i : Set X)).f n).hom := by
    apply (AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport.Cycles.mem_subspaceChainInclusion_range_iff X (U i : Set X) n c).mpr
    intro σ hσ
    exact hi σ (Finsupp.mem_support_iff.mpr hσ)
  obtain ⟨b, hb⟩ := hc
  exact ⟨i, b, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- The genuine chain group in every degree has the colimit universal
property, as proved from finite support and injectivity of open inclusions. -/
def increasingOpenChainDegreeIsColimit (n : ℕ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapCocone
      (increasingOpenChainCocone U hmono)) := by
  apply isColimitOfReflects (forget (ModuleCat.{0} ℤ))
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro c
    obtain ⟨i, b, hb⟩ := exists_increasingOpenChain_lift U hmono hcover n c
    exact ⟨i, b, hb.symm⟩
  · intro i a b hab
    have heq : a = b := singularOpenChainInclusion_injective (U i) n hab
    subst b
    exact ⟨i, 𝟙 i, rfl⟩

/-- The actual chain complex is the colimit, with its actual alternating
face differential. No chain-colimit comparison is assumed. -/
def increasingOpenChainIsColimit :
    IsColimit (increasingOpenChainCocone U hmono) :=
  HomologicalComplex.isColimitOfEval _ _ (increasingOpenChainDegreeIsColimit U hmono hcover)

/-- The canonical chain-complex isomorphism from the increasing open union. -/
def increasingOpenChainColimitIso :
    colimit (increasingOpenChainDiagram U hmono) ≅ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X :=
  (colimit.isColimit _).coconePointUniqueUpToIso (increasingOpenChainIsColimit U hmono hcover)

@[reassoc (attr := simp)]
theorem increasingOpenChainColimitIso_ι (i : ℕ) :
    colimit.ι (increasingOpenChainDiagram U hmono) i ≫
        (increasingOpenChainColimitIso U hmono hcover).hom =
      singularOpenChainInclusion (U i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- The comparison in every degree takes a represented chain to its actual
image under the open-subspace inclusion. -/
theorem increasingOpenChainColimitIso_degree (i n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i))).X n) :
    (increasingOpenChainColimitIso U hmono hcover).hom.f n
        ((colimit.ι (increasingOpenChainDiagram U hmono) i).f n c) =
      (singularOpenChainInclusion (U i)).f n c :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (increasingOpenChainColimitIso_ι U hmono hcover i) n) c

/-- The canonical ordinary singular homology comparison on an increasing
open cover is an isomorphism. -/
def increasingOpenHomologyColimitIso (n : ℕ) :
    colimit (increasingOpenChainDiagram U hmono ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) ≅
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n :=
  Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso (increasingOpenChainDiagram U hmono) n ≪≫
    HomologicalComplex.homologyMapIso (increasingOpenChainColimitIso U hmono hcover) n

/-- The homology isomorphism carries each stage class through the homology
map of the actual open-subspace inclusion. -/
@[reassoc (attr := simp)]
theorem increasingOpenHomologyColimitIso_ι (n i : ℕ) :
    colimit.ι (increasingOpenChainDiagram U hmono ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) i ≫
        (increasingOpenHomologyColimitIso U hmono hcover n).hom =
      HomologicalComplex.homologyMap (singularOpenChainInclusion (U i)) n := by
  change colimit.ι _ i ≫ (Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso _ n).hom ≫
    HomologicalComplex.homologyMap (increasingOpenChainColimitIso U hmono hcover).hom n = _
  rw [Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso_ι_assoc, ← HomologicalComplex.homologyMap_comp,
    increasingOpenChainColimitIso_ι]

end FullCover

/-- The actual inclusion of a stage into the open union, with no assumption
that this union is the whole original ambient space. -/
def openUnionStageInclusion (i : ℕ) :
    TopCat.of (U i) ⟶ TopCat.of (⨆ j, U j : Opens X) :=
  (Opens.toTopCat X).map (Opens.leSupr U i)

/-- Pull the increasing family back to its own actual open union. -/
def openUnionPullbackCover (i : ℕ) : Opens (TopCat.of (⨆ j, U j : Opens X)) :=
  (Opens.map (⨆ j, U j : Opens X).inclusion').obj (U i)

include hmono in
theorem openUnionPullbackCover_monotone : Monotone (openUnionPullbackCover U) := by
  intro i j hij x hx
  exact hmono hij hx

theorem openUnionPullbackCover_iSup : (⨆ i, openUnionPullbackCover U i) = ⊤ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The natural projection of a pulled-back stage onto the original stage. -/
def openUnionPullbackToStage (i : ℕ) :
    TopCat.of (openUnionPullbackCover U i) ⟶ TopCat.of (U i) :=
  TopCat.ofHom ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

@[reassoc]
theorem openUnionPullbackToStage_inclusion (i : ℕ) :
    openUnionPullbackToStage U i ≫ openUnionStageInclusion U i =
      (openUnionPullbackCover U i).inclusion' := by
  ext x
  rfl

/-- The native chain cocone on the actual open union. -/
def openUnionChainCocone : Cocone (increasingOpenChainDiagram U hmono) where
  pt := AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (⨆ j, U j : Opens X))
  ι :=
    { app i := AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i)
      naturality i j f := by
        change AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
            ((Opens.toTopCat X).map (hmono.functor.map f)) ≫
            AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U j) =
          AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i) ≫ 𝟙 _
        rw [Category.comp_id, ← Functor.map_comp]
        congr 1 }

/-- Each actual stage embeds injectively in every chain degree of its union. -/
theorem openUnionChainInclusion_injective (i n : ℕ) :
    Function.Injective
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i)).f n) := by
  let : Mono (openUnionStageInclusion U i) :=
    (TopCat.mono_iff_injective _).mpr (by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun x : (⨆ j, U j : Opens X) => (x : X)) hab)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

include hmono in
/-- Finite singular chains in the actual open union already occur in one
original stage. The pulled-back cover only supplies the compactness proof. -/
theorem exists_openUnionChain_lift (n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (⨆ j, U j : Opens X))).X n) :
    ∃ i, ∃ b : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i))).X n,
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i)).f n b = c := by
  obtain ⟨i, b, hb⟩ := exists_increasingOpenChain_lift (openUnionPullbackCover U)
    (openUnionPullbackCover_monotone U hmono) (openUnionPullbackCover_iSup U) n c
  refine ⟨i, (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionPullbackToStage U i)).f n b, ?_⟩
  have hmap : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionPullbackToStage U i) ≫
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i) =
      singularOpenChainInclusion (openUnionPullbackCover U i) := by
    rw [← Functor.map_comp, openUnionPullbackToStage_inclusion]
  exact (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom hmap n) b).trans hb

/-- The degreewise universal property for arbitrary increasing open unions. -/
def openUnionChainDegreeIsColimit (n : ℕ) :
    IsColimit ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapCocone
      (openUnionChainCocone U hmono)) := by
  apply isColimitOfReflects (forget (ModuleCat.{0} ℤ))
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro c
    obtain ⟨i, b, hb⟩ := exists_openUnionChain_lift U hmono n c
    exact ⟨i, b, hb.symm⟩
  · intro i a b hab
    have heq : a = b := openUnionChainInclusion_injective U i n hab
    subst b
    exact ⟨i, 𝟙 i, rfl⟩

/-- The actual singular chain complex commutes with arbitrary increasing
unions of open subsets, with their canonical inclusion maps. -/
def openUnionChainIsColimit : IsColimit (openUnionChainCocone U hmono) :=
  HomologicalComplex.isColimitOfEval _ _ (openUnionChainDegreeIsColimit U hmono)

/-- The canonical chain-complex isomorphism for an arbitrary open union. -/
def openUnionChainColimitIso :
    colimit (increasingOpenChainDiagram U hmono) ≅
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (⨆ j, U j : Opens X)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (openUnionChainIsColimit U hmono)

@[reassoc (attr := simp)]
theorem openUnionChainColimitIso_ι (i : ℕ) :
    colimit.ι (increasingOpenChainDiagram U hmono) i ≫
        (openUnionChainColimitIso U hmono).hom =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ i

/-- The arbitrary-union comparison sends each represented chain to its
actual image in that union, in every degree. -/
theorem openUnionChainColimitIso_degree (i n : ℕ)
    (c : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (U i))).X n) :
    (openUnionChainColimitIso U hmono).hom.f n
        ((colimit.ι (increasingOpenChainDiagram U hmono) i).f n c) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i)).f n c :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (openUnionChainColimitIso_ι U hmono i) n) c

/-- Ordinary integral singular homology commutes with every increasing open
union. The comparison is induced by the actual inclusions of the stages. -/
def openUnionHomologyColimitIso (n : ℕ) :
    colimit (increasingOpenChainDiagram U hmono ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) ≅
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (⨆ j, U j : Opens X))).homology n :=
  Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso (increasingOpenChainDiagram U hmono) n ≪≫
    HomologicalComplex.homologyMapIso (openUnionChainColimitIso U hmono) n

@[reassoc (attr := simp)]
theorem openUnionHomologyColimitIso_ι (n i : ℕ) :
    colimit.ι (increasingOpenChainDiagram U hmono ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) i ≫
        (openUnionHomologyColimitIso U hmono n).hom =
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (openUnionStageInclusion U i)) n := by
  change colimit.ι _ i ≫ (Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso _ n).hom ≫
    HomologicalComplex.homologyMap (openUnionChainColimitIso U hmono).hom n = _
  rw [Topology.Euclidean.FilteredCohomology.Globalization.filteredHomologyComparisonIso_ι_assoc, ← HomologicalComplex.homologyMap_comp,
    openUnionChainColimitIso_ι]

end

end OAI.AlgebraicTopology.Duality.Poincare.SingularOpenUnion
