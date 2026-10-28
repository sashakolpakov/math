/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.LocalHomology.FlattenedSupport

/-! # Neighborhood Pair Image -/

namespace OAI.AlgebraicTopology.Support.NeighborhoodPairImage.Singular

noncomputable section

/-!
# Transporting neighborhood-support pairs through embeddings

An embedding identifies a neighborhood and its support complement with their
images. Only equality of support membership on that neighborhood is required. Open embeddings
therefore transport the cofinal normal neighborhoods of auxiliary algebraic opens to the original
ambient space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (f : M → N) (hf : IsEmbedding f) (W B : Set M) (S : Set N)
  (hS : ∀ w ∈ W, w ∈ B ↔ f w ∈ S)

/-- Let `f: M → N` be an embedding of topological spaces, with subsets `W, B ⊆ M` and `S ⊆ N`.
Assume `w ∈ B` if and only if `f(w) ∈ S` for every `w ∈ W`. Restriction of `f` gives this
homeomorphism `W \ B ≃ f(W) \ S`, with both sets carrying their subspace topologies. -/
def neighborhoodSupportComplementImageHomeomorph :
    {w : W | (w : M) ∉ B} ≃ₜ {v : f '' W | (v : N) ∉ S} :=
  (hf.homeomorphImage W).subtype fun w => not_congr (hS w w.2)

/-- Let `f: M → N` be an embedding of topological spaces, with subsets `W, B ⊆ M` and `S ⊆ N`.
Assume `w ∈ B` if and only if `f(w) ∈ S` for every `w ∈ W`. This is the isomorphism of
topological pairs `(W, W \ B) ≅ (f(W), f(W) \ S)` whose maps on both spaces are restrictions of
`f`. -/
def neighborhoodSupportPairImageIso :
    LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W B ≅
      LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (f '' W) S where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨hf.homeomorphImage W, (hf.homeomorphImage W).continuous⟩)
    (TopCat.ofHom ⟨neighborhoodSupportComplementImageHomeomorph f hf W B S hS,
      (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).continuous⟩)
    (by ext w; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(hf.homeomorphImage W).symm, (hf.homeomorphImage W).symm.continuous⟩)
    (TopCat.ofHom ⟨(neighborhoodSupportComplementImageHomeomorph f hf W B S hS).symm,
      (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).symm.continuous⟩)
    (by ext w; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).left_inv w
    · ext w
      exact (hf.homeomorphImage W).left_inv w
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      exact (neighborhoodSupportComplementImageHomeomorph f hf W B S hS).right_inv w
    · ext w
      exact (hf.homeomorphImage W).right_inv w

/-- Let `f: M → N` be an embedding of topological spaces, with subsets `W, B ⊆ M` and `S ⊆ N`.
Assume `w ∈ B` if and only if `f(w) ∈ S` for every `w ∈ W`. Pullback along `f` gives this
isomorphism of rational vector spaces `H^n(f(W), f(W) \ S; ℚ) ≅ H^n(W, W \ B; ℚ)` in relative
singular cohomology. -/
def neighborhoodSupportPairImageCohomologyIso (n : ℕ) :
    Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (f '' W) S) n ≅
      Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W B) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (Algebra.Homology.LinearDual.HomologicalComplex.linearDualIso
      ((Singular.Cohomology.relativeChainFunctor ℚ).mapIso (neighborhoodSupportPairImageIso f hf W B S hS)))

/-- Let `f: M → N` be an embedding of topological spaces, with subsets `W, B ⊆ M` and `S ⊆ N`.
Assume `w ∈ B` if and only if `f(w) ∈ S` for every `w ∈ W`. This rational linear equivalence
`H^n(f(W), f(W) \ S; ℚ) ≃ H^n(W, W \ B; ℚ)` pulls relative singular cochains back along the
restrictions of `f`. -/
def neighborhoodSupportPairImageCohomologyEquiv (n : ℕ) :
    Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (f '' W) S) n ≃ₗ[ℚ]
      Singular.Cohomology.RelativeCohomology ℚ (LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W B) n :=
  (neighborhoodSupportPairImageCohomologyIso f hf W B S hS n).toLinearEquiv

end

end OAI.AlgebraicTopology.Support.NeighborhoodPairImage.Singular
