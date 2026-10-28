import OAI.RepresentationTheory.Hecke.RadialDilation.AnalyticDilation
import OAI.RepresentationTheory.Hecke.SphericalAction

/-! # Dilation -/

namespace OAI.RepresentationTheory.Hecke.Dilation.GaloisValuation

/-! The elementary scalar lemma has the complete RadialDilation interface.
The native constructor supplies every finite-action and theta hypothesis;
no result-level RadialDilation assumption remains in that construction. -/

universe u v

theorem dilation_proved : SphericalAction.RadialDilationInput :=
  RadialDilation.AnalyticDilation.Analytic.algebraic_dilation_relation

end OAI.RepresentationTheory.Hecke.Dilation.GaloisValuation
