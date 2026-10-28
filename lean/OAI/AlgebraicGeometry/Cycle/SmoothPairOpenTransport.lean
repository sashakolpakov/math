/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Cycle.LocalLocalHomology
import OAI.AlgebraicGeometry.ClosedImmersion.SourceOpenIs
import OAI.AlgebraicTopology.Support.NeighborhoodPairImage

/-! # Smooth Pair Open Transport -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Local purity neighborhoods transported out of ambient opens

The normal-neighborhood construction uses smooth geometry alone. This module transports
its support pairs along an open embedding, so cohomology can still be computed with a
resolution on the original ambient space. The support-membership identity is purely
topological.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.TopologicalSpace

open OAI.AlgebraicTopology.Singular

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- Normal neighborhoods can be computed in any smooth auxiliary ambient open
and then transported to the original topological ambient space. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSupportImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint.Basic.ComplexSchemePoint X → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (ComplexPoint.Basic.Point.map i))
    (z : ComplexPoint.Basic.ComplexSchemePoint Y) (V : Opens M) (hzV : f (ComplexPoint.Basic.Point.map i z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧ f (ComplexPoint.Basic.Point.map i z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint.Basic.ComplexSchemePoint X) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  let W' := ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood X Y i m d z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint.Basic.ComplexSchemePoint X)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportNeighborhood_le X Y i m d z V' hzV hw
  · exact ⟨_, ComplexPoint.Basic.ComplexSchemePoint.mem_smoothClosedSupportNeighborhood X Y i m d z V' hzV, rfl⟩
  · intro n hn
    let : Subsingleton (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
        (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W' : Set (ComplexPoint.Basic.ComplexSchemePoint X))
          (Set.range (ComplexPoint.Basic.Point.map i))) n) :=
      ModuleCat.subsingleton_of_isZero
        (ComplexPoint.Basic.ComplexSchemePoint.smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V' hzV n hn)
    let e := AlgebraicTopology.Support.NeighborhoodPairImage.Singular.neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (ComplexPoint.Basic.Point.map i)) S (fun w _ => by
        rw [← hS]
        rfl) n
    let : Subsingleton (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
        (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

omit [SmoothOfRelativeDimension m Y.hom] in
/-- Fixed-dimensional source opens suffice: the target is restricted by deleting the discarded
closed image, while the resulting neighborhoods and pairs live in the original ambient analytic
space. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSourceOpenNeighborhood
    (A : Y.left.Opens) [SmoothOfRelativeDimension m (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A).hom]
    (z : ComplexPoint.Basic.ComplexSchemePoint (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A))
    (V : Opens (ComplexPoint.Basic.ComplexSchemePoint X))
    (hzV : ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) z ∈ V) :
    ∃ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), W ≤ V ∧
      ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) z ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set (ComplexPoint.Basic.ComplexSchemePoint X))
            (Set.range (ComplexPoint.Basic.Point.map i))) n)) := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  let T := ClosedImmersion.SourceOpen.closedImmersionSourceOpenTarget i.left A
  let j := ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift i.left A
  have hj : j ≫ (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T).hom = (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A).hom := by
    change j ≫ (T.ι ≫ X.hom) = A.ι ≫ Y.hom
    rw [← Category.assoc, ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift_ι, Category.assoc, i.w]
  let jOver : ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A ⟶ ComplexPoint.Basic.ComplexSchemePoint.openScheme X T := Over.homMk j hj
  let : IsClosedImmersion jOver.left :=
    ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift_isClosedImmersion i.left A
  have : SmoothOfRelativeDimension d (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T).hom := by
    change SmoothOfRelativeDimension d (T.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d T.ι X.hom
  have : Smooth (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T).hom :=
    SmoothOfRelativeDimension.smooth d (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T).hom
  let f := ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X T)
  have hS : f ⁻¹' Set.range (ComplexPoint.Basic.Point.map i) = Set.range (ComplexPoint.Basic.Point.map jOver) := by
    rw [ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion_of_comm X Y i,
      ComplexPoint.Basic.ComplexSchemePoint.range_map_of_isImmersion_of_comm (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T) (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A) jOver]
    change _ = (ComplexPoint.Basic.Point.underlying : ComplexPoint.Basic.ComplexSchemePoint (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T) →
      (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T).left) ⁻¹' Set.range j
    rw [ClosedImmersion.SourceOpen.range_closedImmersionSourceOpenLift i.left A]
    rfl
  have he : f (ComplexPoint.Basic.Point.map jOver z) = ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) z := by
    change ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion X T) (ComplexPoint.Basic.Point.map jOver z) = _
    rw [← ComplexPoint.Basic.Point.map_comp_apply]
    exact congrArg (fun k ↦ ComplexPoint.Basic.Point.map k z)
      (Over.OverMorphism.ext (ClosedImmersion.SourceOpen.closedImmersionSourceOpenLift_ι i.left A))
  obtain ⟨W, hWV, hzW, hW⟩ := ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSupportImageNeighborhood
    (ComplexPoint.Basic.ComplexSchemePoint.openScheme X T) (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A) jOver m d f
    (ComplexPoint.Basic.ComplexSchemePoint.isOpenEmbedding_map_open X T) (Set.range (ComplexPoint.Basic.Point.map i)) hS z V (he ▸ hzV)
  exact ⟨W, hWV, he ▸ hzW, hW⟩

omit [SmoothOfRelativeDimension m Y.hom] in
/-- The fixed-dimensional source-open calculation, transported through a further
open embedding. This is the form used by successive closed supports in a larger ambient. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSourceOpenImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint.Basic.ComplexSchemePoint X → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (ComplexPoint.Basic.Point.map i))
    (A : Y.left.Opens) [SmoothOfRelativeDimension m (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A).hom]
    (z : ComplexPoint.Basic.ComplexSchemePoint (ComplexPoint.Basic.ComplexSchemePoint.openScheme Y A))
    (V : Opens M)
    (hzV : f (ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧
      f (ComplexPoint.Basic.Point.map (ComplexPoint.Basic.ComplexSchemePoint.openInclusion Y A ≫ i) z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint.Basic.ComplexSchemePoint X) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  obtain ⟨W', hW'V', hzW', hW'⟩ := ComplexPoint.Basic.ComplexSchemePoint.exists_smoothClosedSourceOpenNeighborhood
    X Y i m d A z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint.Basic.ComplexSchemePoint X)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ⟨_, hzW', rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hW'V' hw
  · intro n hn
    let : Subsingleton (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
        (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W' : Set (ComplexPoint.Basic.ComplexSchemePoint X))
          (Set.range (ComplexPoint.Basic.Point.map i))) n) := ModuleCat.subsingleton_of_isZero (hW' n hn)
    let e := AlgebraicTopology.Support.NeighborhoodPairImage.Singular.neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (ComplexPoint.Basic.Point.map i)) S (fun w _ => by rw [← hS]; rfl) n
    let : Subsingleton (AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
        (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

end

end OAI.AlgebraicGeometry
