import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PowerEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.ArbitraryBaseChange

/-! # Framed Embedding Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedEmbeddingCoverage.StableHilbertCoverage

noncomputable section

/-! A complete uniform graph embedding with frames at its marked
fibers is normalized on an actual covering family of determinant opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] (B : Over (Spec (.of R)))
variable [IsAffine B.left] [IsLocallyNoetherian B.left]
variable {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left)

theorem framed_uniformEmbedding_normalized_cover
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(B.left, ⊤)))
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hd : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
    (hcomplete : E.HasCompleteSections)
    (e : ∀ z : Fin (N ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex A.level z)).sheaf ≅
        Line.Bundles.structureModule B.left)
    (i : Fin (N ^ (2 * g))) :
    ∃ C : Scheme.OpenCover.{0} B.left,
      (∀ j, IsAffine (C.X j)) ∧ (∀ j, IsNoetherianRing Γ(C.X j, ⊤)) ∧
      ∀ j, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f j ≫ B.hom))
        (A.pullback (C.f j)) i) := by
  let : IsNoetherianRing Γ(B.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top B.left⟩
  let E₀ := E.canonicalDegree (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) hd
  let D₀ : E₀.CompleteSectionData :=
    hcomplete.some.canonicalDegreeData E (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) hd
  have hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
      A.uniformFrameLineBundle.sheaf E₀.sections (𝟙 B.left) := by
    intro K _ q
    exact A.completeGraphEmbedding_universalSections hN hunit E₀ D₀ (Spec (.of K)) q
  have hr : E₀.dimension + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ :=
    (congrArg (fun k => k + 1) hn).trans
      (Nat.sub_add_cancel (Nat.succ_le_of_lt (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ)))
  let C := A.stableFrameOpenCover hg hδ hN hunit hlarge hr E₀.sections hs e
  have ha (j : C.I₀) : IsAffine (C.X j) :=
    A.stableFrameOpenCover_affine hg hδ hN hunit hlarge hr E₀.sections hs e j
  refine ⟨C, ha, ?_, ?_⟩
  · intro j
    let : IsAffine (C.X j) := ha j
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (C.X j)⟩
  intro j
  let : IsAffine (C.X j) := ha j
  let q := C.f j
  let B' : Over (Spec (.of R)) := Over.mk (q ≫ B.hom)
  let A' := A.pullback q
  let π := pullback.fst A.abelian.scheme.hom q
  let E' := A.graphPowerEmbeddingBaseChange E₀ q
  let y := NormalizedEmbeddingCoverage.StableHilbertCoverage.indexedLevelSection A'
  have hy (z : Fin (N ^ (2 * g))) : (y z).left ≫ π =
      q ≫ A.fullLevelSectionAtIndex A.level z :=
    A.abelian.fullLevelGlobalSection_pullback A.level q (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z)
  let e' := fun z => Family.FramedEvaluationBaseChange.familySectionFrameBaseChange A.uniformFrameLineBundle q π
    (A.fullLevelSectionAtIndex A.level z) (y z).left (hy z) (e z)
  have hm : EmbeddingCoverage.StableHilbertCoverage.embeddingVectors R B' E' y e' =
      (fun z k => q.appTop (A.stableFrameVectors E₀.sections e z k)) := by
    funext z k
    exact Family.FramedEvaluationBaseChange.familyFramedSectionValue_baseChange A.uniformFrameLineBundle q π
      (A.fullLevelSectionAtIndex A.level z) (y z).left (hy z) (e z) (E₀.sections k)
  have hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial
      (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (EmbeddingCoverage.StableHilbertCoverage.embeddingVectors R B' E' y e')) j.exponent) := by
    rw [hm]
    exact A.stableFrameOpenCover_denominator_unit hg hδ hN hunit hlarge hr E₀.sections hs e j
  obtain ⟨a, ha, hpoints⟩ := EmbeddingCoverage.StableHilbertCoverage.exists_chart_normalizing_coordinates R B' E' i j y e' hv
  exact ⟨{
    embedding := E'.changeCoordinates a
    degree_eq := rfl
    dimension_eq := hn
    complete := ha ⟨A.completeGraphPowerEmbeddingBaseChange E₀ q hN hunit D₀⟩
    chartIndex := j
    chartPoint := EmbeddingCoverage.StableHilbertCoverage.embeddingChartPoint R B' E' i j y e' hv
    marked := hpoints }⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedEmbeddingCoverage.StableHilbertCoverage
