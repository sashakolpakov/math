import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.SectionEvaluationData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseUniformLevelConfiguration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.LineBundleEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDualEvaluationFrames

/-! # Evaluation Projective Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The canonical graph-power sections evaluated at the ordered torsion
points contain an actual projective frame whenever the explicit
auxiliary-level square threshold holds. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N n : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionEvaluation_projectiveFrame [IsAlgClosed K] [NeZero n]
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2) :
    ∃ (κ : Type u) (_ : Fintype κ)
      (b : Module.Basis κ K (Module.Dual K
        ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
          (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf))),
      Set.range b ⊆ Set.range (A.fullLevelSectionEvaluation level) ∧
        ∃ j, ∀ k, b.repr (A.fullLevelSectionEvaluation level j) k ≠ 0 := by
  let L := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  let V := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj L.sheaf
  have : Module.Finite K V :=
    A.graphBundle_positivePower_sections_finite_overField (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  have hr : Module.finrank K V = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ :=
    A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)
  apply SparseDualEvaluationFrames.dualEvaluation_projectiveFrame (A.fullLevelSectionEvaluation level)
  · exact hr.symm ▸ Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ
  · intro v hv
    let e := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) L.sheaf
    let a := e.symm v
    have ha : a ≠ 0 := by
      intro h
      apply hv
      have he := congrArg e h
      exact (e.apply_symm_apply v).symm.trans (he.trans (map_zero e))
    have h := A.uniformGraphPower_fullLevel_hyperplanes_sparse hg hδ hN hNk level hlarge a ha
    have heq (i : Multiplicative (Fin (2 * g) → ZMod n)) :
        A.fullLevelSectionEvaluation level i v = 0 ↔
          A.abelian.fullLevelGeometricPoint level i ∉ Ample.LineBundles.sectionNonvanishing a :=
      Rational.LineBundleEvaluation.rationalLineBundleEvaluation_eq_zero A.abelian.scheme.hom L
        ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.left
        ((A.abelian.fullLevelRationalTorsionEquiv level).symm i).val.w v
    change Module.finrank K V * _ < _
    rw [hr]
    simpa only [heq, show Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) =
      n ^ (2 * g) by simp] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
