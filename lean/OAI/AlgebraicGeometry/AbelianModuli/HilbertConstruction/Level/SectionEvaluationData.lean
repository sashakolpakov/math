import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation

/-! # Section Evaluation Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual rational evaluation of the uniform graph-power sections
at an ordered full-level point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N n : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionEvaluation (level : A.abelian.FullLevel n)
    (i : Multiplicative (Fin (2 * g) → ZMod n)) :
    Module.Dual K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) :=
  Rational.LineBundleEvaluation.rationalLineBundleEvaluation A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ))
    ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.left
    ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
