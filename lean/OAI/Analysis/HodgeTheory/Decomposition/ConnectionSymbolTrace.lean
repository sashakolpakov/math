import OAI.Analysis.HodgeTheory.Decomposition.ConnectionTrace
import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction

/-! # Connection Symbol Trace -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ConnectionSymbolTrace.Constructions

noncomputable section

/-! The complete torsion-free cancellation between the connection action
on exterior symbols and the derivative of the volume density. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]

theorem symmetricConnection_symbol_trace (b : Module.Basis ι ℝ E) (n : ℕ)
    (Γ : E →L[ℝ] E →L[ℝ] E) (hΓ : ∀ u v, Γ u v = Γ v u) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    (∑ i, CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) (Γ (b i))
      (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap a)) =
    ∑ i, (LinearMap.toMatrix b b (Γ (b i)).toLinearMap).trace •
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap a := by
  simp_rw [CovectorSymbolAction.Constructions.covectorInfinitesimalAction_exteriorSymbol]
  rw [Finset.sum_add_distrib, ConnectionTrace.Constructions.symmetricConnection_alternated_action b n Γ hΓ a, add_zero]
  have h := congrArg (fun ξ : E →L[ℝ] ℝ => CovectorSymbolAction.Constructions.exteriorSymbolBilinear n ξ a)
    (ConnectionTrace.Constructions.symmetricConnection_trace_covector b Γ hΓ)
  simp only [map_sum, map_smul, sum_apply, smul_apply, CovectorSymbolAction.Constructions.exteriorSymbolBilinear_apply] at h
  exact h.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.ConnectionSymbolTrace.Constructions
