import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDecomposition
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportInsideMaps
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Compact Support Pair Index -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairIndex

noncomputable section

/-!
# Actual compact-pair indexing for compact-support Mayer--Vietoris

Pairs of compact sets inside two opens index the intersection, the two
individual supports, and their union. Each corresponding index functor is
final. The maps below are the existing support-enlargement maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}}

/-- Compact subsets contained in an open form a nonempty filtered category. -/
theorem compactSupportsInside_isFiltered (U : Opens X) : IsFiltered U.compactsInside := by
  let : IsDirectedOrder U.compactsInside := CompactSupportDecomposition.compactSupportsInside_directed U
  let : Nonempty U.compactsInside := ⟨⟨⊥, Set.empty_subset _⟩⟩
  infer_instance

/-- The genuine compact intersection, regarded as a support in the open intersection. -/
def compactPairIntersection [T2Space X] (U V : Opens X) :
    U.compactsInside × V.compactsInside → (U ⊓ V).compactsInside :=
  fun p => ⟨p.1.val ⊓ p.2.val, fun _ hx => ⟨p.1.property hx.1, p.2.property hx.2⟩⟩

@[simp]
theorem compactPairIntersection_val [T2Space X] (U V : Opens X)
    (p : U.compactsInside × V.compactsInside) :
    (compactPairIntersection U V p).val = p.1.val ⊓ p.2.val := rfl

theorem compactPairIntersection_monotone [T2Space X] (U V : Opens X) :
    Monotone (compactPairIntersection U V) := by
  intro p q hpq
  exact inf_le_inf (show p.1.val ≤ q.1.val from hpq.1)
    (show p.2.val ≤ q.2.val from hpq.2)

/-- Every compact support in the intersection is the intersection of a pair:
use that same compact set in each open. -/
theorem compactPairIntersection_surjective [T2Space X] (U V : Opens X) :
    Function.Surjective (compactPairIntersection U V) := by
  intro K
  refine ⟨(⟨K.val, fun _ hx => (K.property hx).1⟩,
    ⟨K.val, fun _ hx => (K.property hx).2⟩), ?_⟩
  apply Subtype.ext
  change K.val ⊓ K.val = K.val
  exact inf_idem K.val

/-- The actual compact-intersection index functor. -/
def compactPairIntersectionFunctor [T2Space X] (U V : Opens X) :
    (U.compactsInside × V.compactsInside) ⥤ (U ⊓ V).compactsInside where
  obj := compactPairIntersection U V
  map f := homOfLE ((compactPairIntersection_monotone U V) ⟨leOfHom f.1, leOfHom f.2⟩)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem compactPairIntersectionFunctor_final [T2Space X] (U V : Opens X) :
    (compactPairIntersectionFunctor U V).Final := by
  let : IsDirectedOrder U.compactsInside := CompactSupportDecomposition.compactSupportsInside_directed U
  let : IsDirectedOrder V.compactsInside := CompactSupportDecomposition.compactSupportsInside_directed V
  apply Functor.final_of_exists_of_isFiltered
  · intro K
    obtain ⟨p, rfl⟩ := compactPairIntersection_surjective U V K
    exact ⟨p, ⟨homOfLE le_rfl⟩⟩
  · intro _ p _ _
    exact ⟨p, 𝟙 p, Subsingleton.elim _ _⟩

variable {R : Type} [Ring R]

/-- Left-support relative cohomology indexed by actual compact pairs. -/
abbrev compactSupportPairLeftDiagram (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :=
  CategoryTheory.Prod.fst U.compactsInside V.compactsInside ⋙ CompactSupportInsideMaps.compactSupportInsideDiagram M U n

/-- Right-support relative cohomology indexed by actual compact pairs. -/
abbrev compactSupportPairRightDiagram (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :=
  CategoryTheory.Prod.snd U.compactsInside V.compactsInside ⋙ CompactSupportInsideMaps.compactSupportInsideDiagram M V n

/-- Relative cohomology on the actual compact intersection. -/
abbrev compactSupportPairIntersectionDiagram [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :=
  compactPairIntersectionFunctor U V ⋙ CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊓ V) n

/-- Relative cohomology on the actual compact union. -/
abbrev compactSupportPairUnionDiagram (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :=
  CompactSupportDecomposition.compactPairUnionFunctor U V ⋙ CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊔ V) n

/-- Reindexing by compact pairs preserves the left compact-support colimit. -/
def compactSupportPairLeftColimitIso (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimit (compactSupportPairLeftDiagram M U V n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M U n := by
  let : IsFiltered V.compactsInside := compactSupportsInside_isFiltered V
  exact Functor.Final.colimitIso (CategoryTheory.Prod.fst U.compactsInside V.compactsInside)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M U n)

/-- Reindexing by compact pairs preserves the right compact-support colimit. -/
def compactSupportPairRightColimitIso (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimit (compactSupportPairRightDiagram M U V n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M V n := by
  let : IsFiltered U.compactsInside := compactSupportsInside_isFiltered U
  exact Functor.Final.colimitIso (CategoryTheory.Prod.snd U.compactsInside V.compactsInside)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M V n)

/-- Reindexing by compact intersections preserves the intersection colimit. -/
def compactSupportPairIntersectionColimitIso [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimit (compactSupportPairIntersectionDiagram M U V n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M (U ⊓ V) n := by
  let : (compactPairIntersectionFunctor U V).Final := compactPairIntersectionFunctor_final U V
  exact Functor.Final.colimitIso (compactPairIntersectionFunctor U V)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊓ V) n)

/-- The proved compact decomposition computes the union colimit by compact pairs. -/
def compactSupportPairUnionColimitIso [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ) :
    colimit (compactSupportPairUnionDiagram M U V n) ≅
      CompactSupportInsideMaps.compactSupportedInsideCohomology M (U ⊔ V) n := by
  let : (CompactSupportDecomposition.compactPairUnionFunctor U V).Final := CompactSupportDecomposition.compactPairUnionFunctor_final U V
  exact Functor.Final.colimitIso (CompactSupportDecomposition.compactPairUnionFunctor U V)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊔ V) n)

@[reassoc (attr := simp)]
theorem compactSupportPairLeftColimitIso_ι (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (compactSupportPairLeftDiagram M U V n) p ≫
        (compactSupportPairLeftColimitIso M U V n).hom =
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) p.1 := by
  let : IsFiltered V.compactsInside := compactSupportsInside_isFiltered V
  exact Functor.Final.ι_colimitIso_hom
    (CategoryTheory.Prod.fst U.compactsInside V.compactsInside)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M U n) p

@[reassoc (attr := simp)]
theorem compactSupportPairRightColimitIso_ι (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (compactSupportPairRightDiagram M U V n) p ≫
        (compactSupportPairRightColimitIso M U V n).hom =
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M V n) p.2 := by
  let : IsFiltered U.compactsInside := compactSupportsInside_isFiltered U
  exact Functor.Final.ι_colimitIso_hom
    (CategoryTheory.Prod.snd U.compactsInside V.compactsInside)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M V n) p

@[reassoc (attr := simp)]
theorem compactSupportPairIntersectionColimitIso_ι [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (compactSupportPairIntersectionDiagram M U V n) p ≫
        (compactSupportPairIntersectionColimitIso M U V n).hom =
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊓ V) n) (compactPairIntersection U V p) := by
  let : (compactPairIntersectionFunctor U V).Final := compactPairIntersectionFunctor_final U V
  exact Functor.Final.ι_colimitIso_hom (compactPairIntersectionFunctor U V)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊓ V) n) p

@[reassoc (attr := simp)]
theorem compactSupportPairUnionColimitIso_ι [T2Space X]
    (M : ModuleCat.{0} R) (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (compactSupportPairUnionDiagram M U V n) p ≫
        (compactSupportPairUnionColimitIso M U V n).hom =
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊔ V) n) (CompactSupportDecomposition.compactPairUnion U V p) := by
  let : (CompactSupportDecomposition.compactPairUnionFunctor U V).Final := CompactSupportDecomposition.compactPairUnionFunctor_final U V
  exact Functor.Final.ι_colimitIso_hom (CompactSupportDecomposition.compactPairUnionFunctor U V)
    (CompactSupportInsideMaps.compactSupportInsideDiagram M (U ⊔ V) n) p

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairIndex
