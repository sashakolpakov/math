import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EndomorphismEquationLoci

/-! # Alternative -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Alternative.AlternativeStrategies

noncomputable section

/-! Genuine upstream theorems available to alternative IntegralModel constructions.
The Presentations bridge retains every natural hypothesis and its arbitrary universe.
It adds no moduli realization or compatibility hypothesis. -/

universe u

theorem provedEndomorphismEquationsInput : Presentations.Hilbert.EndomorphismEquationsInput :=
  HilbertScheme.Presentations.EndomorphismEquationLoci.Core.endomorphism_equation_loci

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Alternative.AlternativeStrategies
