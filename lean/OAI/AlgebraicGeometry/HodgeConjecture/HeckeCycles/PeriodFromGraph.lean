import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq

/-! # Period From Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PeriodFromGraph.CM

noncomputable section

/-! A matrix containing the transformed positive graph is uniquely the
fractional-linear transform of the original Siegel period. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_eq (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (W : Matrix I I ℂ)
    (h : ∀ x : I → ℂ, ∃ y : I → ℂ,
      S.val.map (algebraMap ℚ ℂ) *ᵥ Source.UnitaryEq.CM.PeriodCovariance.graphPhase Z x = Sum.elim (W.mulVec y) y) :
    W = ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).transformSiegel Z).matrix := by
  have hm : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).complexify.numerator Z.matrix =
      W * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).complexify.denominator Z.matrix := by
    apply Matrix.mulVec_injective
    funext x
    obtain ⟨y, hy⟩ := h x
    rw [Source.UnitaryEq.CM.PeriodCovariance.block_graph_action] at hy
    have h1 := congrArg (fun f : (I ⊕ I) → ℂ => fun i => f (.inl i)) hy
    have h2 := congrArg (fun f : (I ⊕ I) → ℂ => fun i => f (.inr i)) hy
    rw [← Matrix.mulVec_mulVec]
    exact h1.trans (congrArg W.mulVec h2.symm)
  change W = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).complexify.numerator Z.matrix *
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).complexify.denominator Z.matrix)⁻¹
  rw [hm, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).denominator_det_isUnit Z), Matrix.mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PeriodFromGraph.CM
