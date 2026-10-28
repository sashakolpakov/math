import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy

/-! # Weak Graph Inversion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakGraphInversion.Constructions

noncomputable section

/-! Normalized weak inversion stated in the ambient graph Hilbert space. -/

theorem graph_weak_poisson_normalized {E H W : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (J : E →L[ℂ] H) (D : E →L[ℂ] W) (hJ : IsCompactOperator J)
    (hgraph : ∀ u v, inner ℂ u v = inner ℂ (J u) (J v) + inner ℂ (D u) (D v))
    (f : H) (hf : ∀ k, D k = 0 → inner ℂ f (J k) = 0) :
    ∃! u : E, (∀ k, D k = 0 → inner ℂ k u = 0) ∧ ∀ v, inner ℂ (D u) (D v) = inner ℂ f (J v) := by
  obtain ⟨u, hu, huniq⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy.CM.Construction.graphEnergy_weak_existsUnique_orthogonal J D hJ hgraph
    ((innerSL ℂ f).comp J) hf
  have hn : ∀ k, D k = 0 → inner ℂ k u.val = 0 := u.property
  refine ⟨u.val, ⟨hn, hu⟩, fun v hv => ?_⟩
  exact congrArg Subtype.val (huniq ⟨v, hv.1⟩ hv.2)

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakGraphInversion.Constructions
