import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EvaluationCoverage

/-! # Framed Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedCoverage

noncomputable section

/-! Actual complete graph-power coordinates and actual marked-fiber
frames produce the stable principal-open cover at the original level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators Classical
universe u

theorem graphUniformEmbeddingSectionRank_two_le {g : ℕ} (δ : Fin g → ℕ)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) :
    2 ≤ Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ := by
  have htwo : 2 ≤ (2 : ℕ) ^ g := by
    simpa only [pow_one] using pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hg
  have hp : 1 ≤ ∏ i, δ i := Nat.succ_le_of_lt (Finset.prod_pos (fun i _ => hδ i))
  have hd : 1 ≤ Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ^ g :=
    Nat.succ_le_of_lt (pow_pos (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) g)
  simpa only [Nat.mul_one, Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank] using
    Nat.mul_le_mul (Nat.mul_le_mul htwo hp) hd

namespace PolarizedAbelianWithFullLevel
variable {S : Scheme.{u}} {g N r : ℕ} {δ : Fin g → ℕ} [NeZero N]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(S, ⊤)))
variable (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
variable (hr : r = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
variable (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
variable (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom A.uniformFrameLineBundle.sheaf s (𝟙 S))
variable (e : ∀ z : Fin (N ^ (2 * g)),
  (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex A.level z)).sheaf ≅ Line.Bundles.structureModule S)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.stableFrameVectors : Fin (N ^ (2 * g)) → Fin r → Γ(S, ⊤) :=
  fun z k => Family.FramedSectionEvaluation.familyFramedSectionValue A.uniformFrameLineBundle
    (A.fullLevelSectionAtIndex A.level z) (e z) (s k)

include hg hN in
omit [NeZero N] in
private theorem originalLevel_points_two_le : 2 ≤ N ^ (2 * g) := by
  have h := pow_le_pow_right' (show 1 ≤ N by omega) (show 1 ≤ 2 * g by omega)
  exact (show 2 ≤ N by omega).trans (by simpa only [pow_one] using h)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.stableFrameOpenCover : Scheme.OpenCover.{0} S :=
  FrameCoverage.StableHilbertCoverage.frameOpenCover (A.stableFrameVectors s e)
    (hr.symm ▸ graphUniformEmbeddingSectionRank_two_le δ hg hδ)
    (originalLevel_points_two_le hg hN)
    (fun K _ _ q => (A.uniformSectionMatrix_geometric_stable hg hδ hN hunit A.level
      hlarge hr s hs e K q).1)
    (fun K _ _ q => (A.uniformSectionMatrix_geometric_stable hg hδ hN hunit A.level
      hlarge hr s hs e K q).2)

instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.stableFrameOpenCover_affine [IsAffine S]
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r (N ^ (2 * g))) :
    IsAffine ((A.stableFrameOpenCover hg hδ hN hunit hlarge hr s hs e).X j) :=
  inferInstanceAs (IsAffine (S.basicOpen (FrameCoverage.StableHilbertCoverage.frameDenominator
    (A.stableFrameVectors s e) j)).toScheme)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.stableFrameOpenCover_denominator_unit
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r (N ^ (2 * g))) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k =>
      ((A.stableFrameOpenCover hg hδ hN hunit hlarge hr s hs e).f j).appTop
        (A.stableFrameVectors s e z k))) j.exponent) :=
  FrameCoverage.StableHilbertCoverage.frameOpenCover_denominator_unit (A.stableFrameVectors s e)
    (hr.symm ▸ graphUniformEmbeddingSectionRank_two_le δ hg hδ)
    (originalLevel_points_two_le hg hN)
    (fun K _ _ q => (A.uniformSectionMatrix_geometric_stable hg hδ hN hunit A.level
      hlarge hr s hs e K q).1)
    (fun K _ _ q => (A.uniformSectionMatrix_geometric_stable hg hδ hN hunit A.level
      hlarge hr s hs e K q).2) j

end PolarizedAbelianWithFullLevel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedCoverage
