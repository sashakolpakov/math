import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension
import OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Relative Neighborhood Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback

noncomputable section

/-! # Actual maps of support-neighborhood pairs retain the actual normal projection coclass -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Singular

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

/-- The genuine inclusion of a support-neighborhood pair in the ambient subset pair. -/
def neighborhoodToSubsetPair (W B : Set M) :
    AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W B ⟶ TopPair.ofSubset (X := TopCat.of M) Bᶜ :=
  RelativeDualAbsoluteExtension.originalSubsetPairMap (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (fun _ h => h)

/-- Both maps are the original continuous map restricted to the actual pair subspaces. -/
def neighborhoodSupportPairMap (f : C(M, N)) (B : Set M) (S : Set N)
    (hB : f ⁻¹' S = B) (W : Set M) (U : Set N) (hWU : Set.MapsTo f W U) :
    AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair W B ⟶ AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair U S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨f w.val, hWU w.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨f w.val.val, hWU w.val.property⟩,
      fun h => w.property ((congrArg (fun T : Set M => w.val.val ∈ T) hB).mp h)⟩,
      ((f.continuous.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _
        |>.subtype_mk _⟩)
    (by ext w; rfl)

theorem neighborhoodSupportPairMap_toSubset (f : C(M, N)) (B : Set M) (S : Set N)
    (hB : f ⁻¹' S = B) (W : Set M) (U : Set N) (hWU : Set.MapsTo f W U) :
    neighborhoodSupportPairMap f B S hB W U hWU ≫ neighborhoodToSubsetPair U S =
    neighborhoodToSubsetPair W B ≫
      RelativeDualAbsoluteExtension.originalSubsetPairMap (A := Bᶜ) (B := Sᶜ) (TopCat.ofHom f) (by
        intro y hy
        change f y ∉ S
        intro h
        exact hy ((congrArg (fun T : Set M => y ∈ T) hB).mp h)) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

theorem neighborhoodSupportPairMap_restrict (f : C(M, N)) (B : Set M) (S : Set N)
    (hB : f ⁻¹' S = B) {W W' : Set M} {U U' : Set N}
    (hW : W' ⊆ W) (hU : U' ⊆ U) (hWU : Set.MapsTo f W U)
    (hWU' : Set.MapsTo f W' U') :
    neighborhoodSupportPairMap f B S hB W' U' hWU' ≫
      AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hU S =
    AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap hW B ≫
      neighborhoodSupportPairMap f B S hB W U hWU := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem chartNormalCoclass_pullback (p : ℕ) (f : C(M, N)) (B : Set M) (S : Set N)
    (hB : f ⁻¹' S = B)
    (e : OpenPartialHomeomorph M (E × (Fin p → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin p → ℂ)))
    (he : ∀ y ∈ e.source, y ∈ B ↔ (e y).2 = 0)
    (hd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (W : Set M) (U : Set N) (hWU : Set.MapsTo f W U)
    (hW : W ⊆ e.source) (hU : U ⊆ d.source)
    (hcoord : ∀ y ∈ W, (e y).2 = (d (f y)).2) :
    AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p) (neighborhoodSupportPairMap f B S hB W U hWU)
      (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass F p d S hd U hU) =
    AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E p e B he W hW := by
  have hp : neighborhoodSupportPairMap f B S hB W U hWU ≫
      AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair F p d S hd U hU =
    AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionPair E p e B he W hW := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      change (d (f w.val.val)).2 = (e w.val.val).2
      exact hcoord w.val.val w.val.property |>.symm
    · ext w
      change (d (f w.val)).2 = (e w.val).2
      exact hcoord w.val w.property |>.symm
  unfold AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, hp]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback
