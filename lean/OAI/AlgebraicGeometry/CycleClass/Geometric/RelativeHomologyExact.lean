import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Relative Homology Exact -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles

noncomputable section

/-!
# The long exact sequence of integral singular homology of a pair

The boundary maps below are the connecting morphisms of the proved short exact
sequence of genuine singular chain complexes. No local orientation, excision,
or fundamental-class assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Ordinary integral singular homology, computed from mathlib's singular chains. -/
abbrev integralSingularHomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  (LocalHomology.Cycles.integralSingularChains X).homology n

/-- The homology map of a continuous map on genuine integral singular chains. -/
abbrev integralSingularHomologyMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    integralSingularHomology X n ⟶ integralSingularHomology Y n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.integralSingularChainFunctor.map f) n

/-- The homology map induced by the inclusion of the subspace. -/
abbrev subspaceHomologyInclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    integralSingularHomology (TopCat.of A) n ⟶ integralSingularHomology X n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.subspaceChainInclusion X A) n

/-- The map from absolute homology to homology relative to the subspace. -/
abbrev relativeHomologyProjection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    integralSingularHomology X n ⟶ LocalHomology.Cycles.relativeSingularHomology X A n :=
  HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X A) n

/-- The genuine connecting boundary `H_(n+1)(X,A;ℤ) → H_n(A;ℤ)`. -/
def relativeHomologyBoundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LocalHomology.Cycles.relativeSingularHomology X A (n + 1) ⟶
      integralSingularHomology (TopCat.of A) n :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem subspaceHomologyInclusion_projection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    subspaceHomologyInclusion X A n ≫ relativeHomologyProjection X A n = 0 := by
  change HomologicalComplex.homologyMap (LocalHomology.Cycles.subspaceChainInclusion X A) n ≫
    HomologicalComplex.homologyMap (LocalHomology.Cycles.relativeChainProjection X A) n = 0
  rw [← HomologicalComplex.homologyMap_comp, LocalHomology.Cycles.subspaceChainInclusion_projection,
    HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
theorem relativeHomologyProjection_boundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeHomologyProjection X A (n + 1) ≫ relativeHomologyBoundary X A n = 0 :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).comp_δ (n + 1) n rfl

@[reassoc (attr := simp)]
theorem relativeHomologyBoundary_inclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    relativeHomologyBoundary X A n ≫ subspaceHomologyInclusion X A n = 0 :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δ_comp (n + 1) n rfl

/-- Exactness at absolute homology in every degree, including degree zero. -/
theorem relativeHomology_exact_absolute (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (subspaceHomologyInclusion X A n)
      (relativeHomologyProjection X A n)
      (subspaceHomologyInclusion_projection X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₂ n

/-- Exactness at positive-degree relative homology. -/
theorem relativeHomology_exact_relative (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeHomologyProjection X A (n + 1))
      (relativeHomologyBoundary X A n)
      (relativeHomologyProjection_boundary X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₃ (n + 1) n rfl

/-- Exactness at subspace homology in every degree, including degree zero. -/
theorem relativeHomology_exact_subspace (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relativeHomologyBoundary X A n)
      (subspaceHomologyInclusion X A n)
      (relativeHomologyBoundary_inclusion X A n)).Exact :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).homology_exact₁ (n + 1) n rfl

/-- An absolute class comes from the subspace exactly when its relative class vanishes. -/
theorem relativeHomology_range_inclusion (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (subspaceHomologyInclusion X A n).hom =
      LinearMap.ker (relativeHomologyProjection X A n).hom :=
  (relativeHomology_exact_absolute X A n).moduleCat_range_eq_ker

/-- A positive-degree relative class lifts absolutely exactly when its boundary vanishes. -/
theorem relativeHomology_range_projection (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeHomologyProjection X A (n + 1)).hom =
      LinearMap.ker (relativeHomologyBoundary X A n).hom :=
  (relativeHomology_exact_relative X A n).moduleCat_range_eq_ker

/-- A subspace class bounds relatively exactly when its image in the ambient space vanishes. -/
theorem relativeHomology_range_boundary (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.range (relativeHomologyBoundary X A n).hom =
      LinearMap.ker (subspaceHomologyInclusion X A n).hom :=
  (relativeHomology_exact_subspace X A n).moduleCat_range_eq_ker

/-- The degree-zero absolute-to-relative map is surjective. -/
instance relativeHomologyProjection_zero_epi (X : TopCat.{0}) (A : Set X) :
    Epi (relativeHomologyProjection X A 0) := by
  apply HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
  intro j hj
  exact Nat.succ_ne_zero j hj

/-- A map of topological pairs induces a morphism of the actual short exact chain sequences. -/
def relativeChainSequenceMap {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    LocalHomology.Cycles.relativeChainSequence X A ⟶ LocalHomology.Cycles.relativeChainSequence Y B where
  τ₁ := LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceMap f h)
  τ₂ := LocalHomology.Cycles.integralSingularChainFunctor.map f
  τ₃ := LocalHomology.Cycles.relativeSingularChainsMap f h
  comm₁₂ := by
    change LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceMap f h) ≫
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion Y B) =
      LocalHomology.Cycles.integralSingularChainFunctor.map (LocalHomology.Cycles.subspaceInclusion X A) ≫
        LocalHomology.Cycles.integralSingularChainFunctor.map f
    rw [← Functor.map_comp, ← Functor.map_comp, LocalHomology.Cycles.subspaceMap_inclusion]
  comm₂₃ := (LocalHomology.Cycles.relativeChainProjection_naturality f h).symm

/-- Connecting boundaries commute with continuous maps of pairs. -/
@[reassoc]
theorem relativeHomologyBoundary_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ) :
    relativeHomologyBoundary X A n ≫
        integralSingularHomologyMap (LocalHomology.Cycles.subspaceMap f h) n =
      LocalHomology.Cycles.relativeSingularHomologyMap f h (n + 1) ≫ relativeHomologyBoundary Y B n :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeChainSequenceMap f h)
    (LocalHomology.Cycles.relativeChainSequence_shortExact X A) (LocalHomology.Cycles.relativeChainSequence_shortExact Y B)
    (n + 1) n rfl

/-- When two ambient homology groups vanish, the actual relative boundary is an isomorphism. -/
def relativeHomologyBoundaryIso (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (integralSingularHomology X (n + 1)))
    (hj : IsZero (integralSingularHomology X n)) :
    LocalHomology.Cycles.relativeSingularHomology X A (n + 1) ≅
      integralSingularHomology (TopCat.of A) n :=
  (LocalHomology.Cycles.relativeChainSequence_shortExact X A).δIso (n + 1) n rfl hi hj

@[simp]
theorem relativeHomologyBoundaryIso_hom (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (hi : IsZero (integralSingularHomology X (n + 1)))
    (hj : IsZero (integralSingularHomology X n)) :
    (relativeHomologyBoundaryIso X A n hi hj).hom = relativeHomologyBoundary X A n := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeHomologyExact.Cycles
