import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedEvaluationBaseChange

/-! # Family Evaluation Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual uniform graph line bundle, ordered marked sections,
and their framed evaluation matrix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

abbrev PolarizationData.PolarizedAbelianWithFullLevel.uniformFrameLineBundle : Line.Bundles.LineBundle A.abelian.scheme.left :=
  A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionAtIndex (level : A.abelian.FullLevel n) (i : Fin (n ^ (2 * g))) :
    S ⟶ A.abelian.scheme.left :=
  A.abelian.fullLevelGlobalSection level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := n) i)

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelFamilyEvaluationMatrix (level : A.abelian.FullLevel n)
    (s : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
    (e : ∀ i : Fin (n ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex level i)).sheaf ≅ Line.Bundles.structureModule S) :
    Fin (n ^ (2 * g)) → Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) → Γ(S, ⊤) :=
  fun i k => Family.FramedSectionEvaluation.familyFramedSectionValue A.uniformFrameLineBundle (A.fullLevelSectionAtIndex level i) (e i) (s k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
