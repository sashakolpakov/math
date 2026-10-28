import OAI.Analysis.HodgeTheory.Decomposition.CompactInclusion
import OAI.Analysis.HodgeTheory.Decomposition.WeakGraphInversion

/-! # Poisson Operators -/

namespace OAI.Analysis.HodgeTheory.Decomposition.PoissonOperators.Constructions

noncomputable section

/-! Specialization of abstract weak inversion to the genuine Hodge graph
operators, with the operator, compactness, and graph identities checked separately. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

-- These proof abbreviations retain the elaborator's inferred instance
-- parameters. All bodies are supplied and fully kernel checked.
abbrev projectiveGraphWeakSolver :=
  WeakGraphInversion.Constructions.graph_weak_poisson_normalized (E := EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (H := Form.Constructions.ProjectiveL2Forms V (n + 1)) (W := EnergyDomain.Constructions.ProjectiveEnergyValues V n)
    (EnergyDomain.Constructions.projectiveEnergyInclusion V n) (EnergyDomain.Constructions.projectiveEnergyDerivative V n)

abbrev projectiveGraphWeakCompactSolver :=
  projectiveGraphWeakSolver V n (CompactInclusion.Constructions.projectiveEnergyInclusion_isCompact V n)

abbrev projectiveGraphWeakEquationSolver :=
  projectiveGraphWeakCompactSolver V n (fun _ _ => rfl)

end

end OAI.Analysis.HodgeTheory.Decomposition.PoissonOperators.Constructions
