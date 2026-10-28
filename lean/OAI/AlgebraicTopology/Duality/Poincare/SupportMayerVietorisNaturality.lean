import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Support Mayer Vietoris Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SupportMayerVietorisNaturality

noncomputable section

/-!
# Naturality of the actual binary relative chain sequence

Increasing each subspace gives the corresponding map of relative chain
quotients and of the quotient by binary small chains. These maps form a
morphism of the proved short exact sequences and commute with the canonical
comparison to relative chains of the union.

For enlargements of supports, apply these results to the reversed inclusions
of their complements before taking the cochain dual.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
open OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles

set_option backward.isDefEq.respectTransparency false

variable (X : TopCat.{0}) {A B A' B' A'' B'' : Set X}

/-- The actual chain inclusion induced by the inclusion of the two binary
small-simplex subcomplexes. -/
def binarySmallChainInclusionMap (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X A B ⟶ AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains X A' B' :=
  AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.integralSimplicialChainFunctor.map (SSet.Subcomplex.homOfLE
    (sup_le_sup (AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion.Cycles.subspaceSingularSubcomplex_mono X hA)
      (AlgebraicGeometry.CycleClass.Geometric.BinarySmallUnion.Cycles.subspaceSingularSubcomplex_mono X hB)))

@[reassoc (attr := simp)]
theorem binarySmallChainInclusionMap_inclusion (hA : A ⊆ A') (hB : B ⊆ B') :
    binarySmallChainInclusionMap X hA hB ≫ AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A' B' =
      AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B := by
  rw [binarySmallChainInclusionMap, AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical,
    AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_eq_canonical, ← Functor.map_comp,
    SSet.Subcomplex.homOfLE_ι]

/-- The genuine map of quotients by binary small chains. -/
def binarySmallComplementMap (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B ⟶ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A' B' :=
  cokernel.map (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)
    (AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A' B')
    (binarySmallChainInclusionMap X hA hB) (𝟙 _)
    (by simp)

@[reassoc (attr := simp)]
theorem binarySmallComplementMap_projection (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B ≫ binarySmallComplementMap X hA hB =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A' B' := by
  simp [binarySmallComplementMap]

@[simp]
theorem relativeSubsetChainMap_refl (A : Set X) :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.Subset.refl A) = 𝟙 _ := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)).mp
  simp

@[reassoc (attr := simp)]
theorem relativeSubsetChainMap_comp (hA : A ⊆ A') (hA' : A' ⊆ A'') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hA ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hA' =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (hA.trans hA') := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)).mp
  simp

@[simp]
theorem binarySmallComplementMap_refl (A B : Set X) :
    binarySmallComplementMap X (Set.Subset.refl A) (Set.Subset.refl B) = 𝟙 _ := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  simp

@[reassoc (attr := simp)]
theorem binarySmallComplementMap_comp (hA : A ⊆ A') (hB : B ⊆ B')
    (hA' : A' ⊆ A'') (hB' : B' ⊆ B'') :
    binarySmallComplementMap X hA hB ≫ binarySmallComplementMap X hA' hB' =
      binarySmallComplementMap X (hA.trans hA') (hB.trans hB') := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  simp

@[reassoc (attr := simp)]
theorem binarySmallComplementLeft_naturality (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A B ≫ binarySmallComplementMap X hA hB =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hA ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementLeft X A' B' := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A)).mp
  simp

@[reassoc (attr := simp)]
theorem binarySmallComplementRight_naturality (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A B ≫ binarySmallComplementMap X hA hB =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hB ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X A' B' := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X B)).mp
  simp

/-- The map of the actual short exact binary relative chain sequences. -/
def binaryRelativeChainSequenceMap (hA : A ⊆ A') (hB : B ⊆ B') :
    AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A B ⟶ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence X A' B' where
  τ₁ := AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB)
  τ₂ := biprod.map (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hA) (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hB)
  τ₃ := binarySmallComplementMap X hA hB
  comm₁₂ := by
    apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X (A ∩ B))).mp
    apply biprod.hom_ext <;> simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
  comm₂₃ := by
    apply biprod.hom_ext' <;> simp [AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]

@[simp]
theorem binaryRelativeChainSequenceMap_τ₁ (hA : A ⊆ A') (hB : B ⊆ B') :
    (binaryRelativeChainSequenceMap X hA hB).τ₁ =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB) := rfl

@[simp]
theorem binaryRelativeChainSequenceMap_τ₂ (hA : A ⊆ A') (hB : B ⊆ B') :
    (binaryRelativeChainSequenceMap X hA hB).τ₂ =
      biprod.map (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hA) (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X hB) := rfl

@[simp]
theorem binaryRelativeChainSequenceMap_τ₃ (hA : A ⊆ A') (hB : B ⊆ B') :
    (binaryRelativeChainSequenceMap X hA hB).τ₃ = binarySmallComplementMap X hA hB := rfl

@[simp]
theorem binaryRelativeChainSequenceMap_refl (A B : Set X) :
    binaryRelativeChainSequenceMap X (Set.Subset.refl A) (Set.Subset.refl B) = 𝟙 _ := by
  apply ShortComplex.hom_ext
  · simp [binaryRelativeChainSequenceMap, AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]
  · apply biprod.hom_ext <;> simp [binaryRelativeChainSequenceMap]
  · simp [binaryRelativeChainSequenceMap, AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence]

@[reassoc (attr := simp)]
theorem binaryRelativeChainSequenceMap_comp (hA : A ⊆ A') (hB : B ⊆ B')
    (hA' : A' ⊆ A'') (hB' : B' ⊆ B'') :
    binaryRelativeChainSequenceMap X hA hB ≫ binaryRelativeChainSequenceMap X hA' hB' =
      binaryRelativeChainSequenceMap X (hA.trans hA') (hB.trans hB') := by
  apply ShortComplex.hom_ext
  · simp [binaryRelativeChainSequenceMap]
  · apply biprod.hom_ext <;> simp [binaryRelativeChainSequenceMap]
  · simp [binaryRelativeChainSequenceMap]

/-- The naturality square with the actual union-relative quotient map. -/
@[reassoc (attr := simp)]
theorem binarySmallComplementToRelative_naturality (hA : A ⊆ A') (hB : B ⊆ B') :
    binarySmallComplementMap X hA hB ≫ AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A' B' =
      AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementToRelative X A B ≫
        AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.union_subset_union hA hB) := by
  apply (cancel_epi (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B)).mp
  simp

/-- Naturality of the connecting homomorphism is now a direct application
of the homology-sequence theorem to the constructed short-complex map. -/
@[reassoc]
theorem binaryRelativeChainSequence_δ_naturality
    (hA : A ⊆ A') (hB : B ⊆ B') (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence_shortExact X A B).δ (n + 1) n rfl ≫
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.relativeSubsetChainMap X (Set.inter_subset_inter hA hB)) n =
    HomologicalComplex.homologyMap (binarySmallComplementMap X hA hB) (n + 1) ≫
      (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence_shortExact X A' B').δ (n + 1) n rfl :=
  HomologicalComplex.HomologySequence.δ_naturality
    (binaryRelativeChainSequenceMap X hA hB)
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence_shortExact X A B)
    (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binaryRelativeChainSequence_shortExact X A' B') (n + 1) n rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.SupportMayerVietorisNaturality
