import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCutoffIdentity

/-! # Real Flux Rearrangement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RealFluxRearrangement

noncomputable section

/-! The three actual lower-order pairings move to the source and flux sides with their exact signs. -/

theorem real_flux_pair_rearrangement {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (p : ℝ) (f c d q : F) (b v : G)
    (h : p + inner ℝ b v + inner ℝ c q + inner ℝ d q = inner ℝ f q) :
    p = inner ℝ (f - c - d) q + inner ℝ (-b) v := by
  simp only [inner_sub_left, inner_neg_left]
  linarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RealFluxRearrangement
