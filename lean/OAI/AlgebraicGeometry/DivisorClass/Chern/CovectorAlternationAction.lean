import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols
import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction

/-! # Covector Alternation Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorAlternationAction

noncomputable section

/-! The actual induced covector action commutes with alternation through both tensor slots. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions _root_.ContinuousAlternatingMap

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem alternation_basis_symbols (b : Module.Basis ι ℝ E) (n : ℕ) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    alternatizeUncurryFin N = ∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap (N (b i)) := by
  simpa only [ContinuousLinearMap.comp_id] using Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.alternation_comp_symbol_expansion b n N (ContinuousLinearMap.id ℝ E)

theorem covectorInfinitesimalAction_alternation (b : Module.Basis ι ℝ E) (n : ℕ)
    (G : E →L[ℝ] E) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) G (alternatizeUncurryFin N) =
      alternatizeUncurryFin (N.comp G) + alternatizeUncurryFin ((Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G).comp N) := by
  rw [alternation_basis_symbols b n N, _root_.map_sum]
  simp_rw [Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.covectorInfinitesimalAction_exteriorSymbol]
  rw [Finset.sum_add_distrib, ← Analysis.HodgeTheory.Decomposition.CovectorSymbolAction.Constructions.alternation_comp_symbol_expansion b n N G,
    alternation_basis_symbols b n ((Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G).comp N)]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorAlternationAction
