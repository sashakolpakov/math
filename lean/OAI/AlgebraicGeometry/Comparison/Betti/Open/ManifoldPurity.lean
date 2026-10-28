import OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence
import OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree

/-! # Manifold Purity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldPurity.Holomorphic

noncomputable section

/-! Pure type under the actual equivalence between open-domain and intrinsic forms. -/

open _root_.TopologicalSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {U : Opens E} {p q : ℕ}

theorem smoothOpenManifoldEquiv_pure_iff (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U (p + q) form).val ↔
      ∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (form x) := by
  constructor
  · intro h x
    have ht : (x : E) ∈ (chartAt E x).target := by
      rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_target]
      exact x.property
    have hp := h (chartAt E x) (chart_mem_atlas E x) x ht
    change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q
      ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv U (p + q) form).inChart (chartAt E x) (x : E)) at hp
    rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart _ _ (chart_mem_atlas E x) x.property,
      Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply] at hp
    exact hp
  · intro h e he y hy
    have hym : y ∈ U := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hy
    change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv U (p + q) form).inChart e y)
    rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart _ _ he hym,
      Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U form ⟨y, hym⟩]
    exact h ⟨y, hym⟩

theorem smoothOpenManifoldEquiv_symm_pure (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U (p + q))
    (hform : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q form.val) :
    ∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U (p + q)).symm form x) := by
  apply (smoothOpenManifoldEquiv_pure_iff _).mp
  simpa only [LinearEquiv.apply_symm_apply] using hform

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldPurity.Holomorphic
