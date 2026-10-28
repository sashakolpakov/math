import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sets.Compacts
import Mathlib.CategoryTheory.Filtered.Final

/-! # Compact Support Decomposition -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDecomposition

noncomputable section

/-!
# Compact support decompositions subordinate to two open sets

The decomposition is constructed by regular separation inside the compact
Hausdorff support itself. Consequently, the ambient space needs only to be
Hausdorff; no ambient normality or locally compact shrinking hypothesis is
assumed. The genuine compact-pair union map is surjective and final.
-/

open Set _root_.TopologicalSpace _root_.CategoryTheory
open scoped _root_.Topology

variable {X : Type*} [TopologicalSpace X]

/-- Regular separation splits a compact set into two compact pieces lying
in the respective members of an open cover. -/
theorem exists_compact_split_of_regular [RegularSpace X]
    {K U V : Set X} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : K ⊆ U ∪ V) :
    ∃ A B : Set X, IsCompact A ∧ IsCompact B ∧ A ⊆ U ∧ B ⊆ V ∧ A ∪ B = K := by
  have hdiff : K \ V ⊆ U := by
    intro x hx
    exact (hcover hx.1).resolve_right hx.2
  obtain ⟨O, hO, hdiffO, hOU⟩ :=
    (hK.diff hV).exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hdiff)
  refine ⟨K ∩ closure O, K \ O, hK.inter_right isClosed_closure, hK.diff hO,
    fun _ hx => hOU hx.2, ?_, ?_⟩
  · intro x hx
    by_contra hxV
    exact hx.2 (hdiffO ⟨hx.1, hxV⟩)
  · apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro x hx
      by_cases hxO : x ∈ O
      · exact Or.inl ⟨hx, subset_closure hxO⟩
      · exact Or.inr ⟨hx, hxO⟩

/-- Every compact support in a two-open union is exactly the union of
compact supports in the respective opens. Regularity is used only on the
compact Hausdorff subtype, so the ambient space needs no further separation
or local compactness assumption. -/
theorem exists_compacts_union_of_subset_union [T2Space X]
    (K : Compacts X) {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : (K : Set X) ⊆ U ∪ V) :
    ∃ A B : Compacts X, (A : Set X) ⊆ U ∧ (B : Set X) ⊆ V ∧ A ⊔ B = K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  obtain ⟨A, B, hA, hB, hAU, hBV, hAB⟩ :=
    exists_compact_split_of_regular (X := K) isCompact_univ
      (hU.preimage continuous_subtype_val) (hV.preimage continuous_subtype_val)
      (fun x _ => hcover x.property)
  let KA : Compacts X := ⟨Subtype.val '' A, hA.image continuous_subtype_val⟩
  let KB : Compacts X := ⟨Subtype.val '' B, hB.image continuous_subtype_val⟩
  refine ⟨KA, KB, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hAU hy
  · rintro x ⟨y, hy, rfl⟩
    exact hBV hy
  · apply Compacts.ext
    change Subtype.val '' A ∪ Subtype.val '' B = (K : Set X)
    rw [← image_union, hAB, image_univ, Subtype.range_val]

/-- The same genuine compact decomposition, stated using ordinary sets. -/
theorem exists_compact_split [T2Space X]
    {K U V : Set X} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : K ⊆ U ∪ V) :
    ∃ A B : Set X, IsCompact A ∧ IsCompact B ∧ A ⊆ U ∧ B ⊆ V ∧ A ∪ B = K := by
  obtain ⟨A, B, hAU, hBV, hAB⟩ :=
    exists_compacts_union_of_subset_union (⟨K, hK⟩ : Compacts X) hU hV hcover
  exact ⟨A, B, A.isCompact, B.isCompact, hAU, hBV,
    congrArg (fun C : Compacts X => (C : Set X)) hAB⟩

/-- Union of the actual compact supports inside the two open sets. -/
def compactPairUnion (U V : Opens X) :
    U.compactsInside × V.compactsInside → (U ⊔ V).compactsInside :=
  fun p => ⟨p.1.val ⊔ p.2.val, by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (p.1.property hx)
    · exact Or.inr (p.2.property hx)⟩

@[simp]
theorem compactPairUnion_val (U V : Opens X) (p : U.compactsInside × V.compactsInside) :
    (compactPairUnion U V p).val = p.1.val ⊔ p.2.val := rfl

theorem compactPairUnion_monotone (U V : Opens X) : Monotone (compactPairUnion U V) := by
  intro p q hpq
  change p.1.val ⊔ p.2.val ≤ q.1.val ⊔ q.2.val
  exact sup_le_sup (show p.1.val ≤ q.1.val from hpq.1)
    (show p.2.val ≤ q.2.val from hpq.2)

/-- Exact compact decomposition says more than order cofinality: the
compact-pair union map is actually surjective on support objects. -/
theorem compactPairUnion_surjective [T2Space X] (U V : Opens X) :
    Function.Surjective (compactPairUnion U V) := by
  intro K
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    exists_compacts_union_of_subset_union K.val U.isOpen V.isOpen K.property
  exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), Subtype.ext hAB⟩

/-- Compact supports inside a fixed open set are directed under union. -/
theorem compactSupportsInside_directed (U : Opens X) : IsDirectedOrder U.compactsInside := by
  constructor
  intro A B
  refine ⟨⟨A.val ⊔ B.val, union_subset A.property B.property⟩, ?_, ?_⟩
  · exact (show A.val ≤ A.val ⊔ B.val from le_sup_left)
  · exact (show B.val ≤ A.val ⊔ B.val from le_sup_right)

/-- The actual functor from pairs of compact supports to their union. -/
def compactPairUnionFunctor (U V : Opens X) :
    (U.compactsInside × V.compactsInside) ⥤ (U ⊔ V).compactsInside where
  obj := compactPairUnion U V
  map f := homOfLE ((compactPairUnion_monotone U V) ⟨leOfHom f.1, leOfHom f.2⟩)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Reindexing a colimit over supports in a two-open union by actual pairs
of supports in the two opens is valid: the union functor is final. -/
theorem compactPairUnionFunctor_final [T2Space X] (U V : Opens X) :
    (compactPairUnionFunctor U V).Final := by
  let : IsDirectedOrder U.compactsInside := compactSupportsInside_directed U
  let : IsDirectedOrder V.compactsInside := compactSupportsInside_directed V
  apply Functor.final_of_exists_of_isFiltered
  · intro K
    obtain ⟨p, rfl⟩ := compactPairUnion_surjective U V K
    exact ⟨p, ⟨homOfLE le_rfl⟩⟩
  · intro _ p _ _
    exact ⟨p, 𝟙 p, Subsingleton.elim _ _⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDecomposition
