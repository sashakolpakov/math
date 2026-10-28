import OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites
import OAI.RepresentationTheory.Weil.Local.Formulas
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Analytic -/

namespace OAI.RepresentationTheory.Hecke.Analytic.GaloisValuation

/-! Use the proved local Weil and Poisson theorems at their complete types. -/

universe u v w x

theorem local_weil_proved : RadialDilation.Prerequisites.Core.LocalWeil.Proposition :=
  Weil.Local.Formulas.schrodinger_generator_formulas

theorem poisson_proved : RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition := by
  intro ι _ _ MpR MpF MpA _ _ _ D γ
  exact Theta.PoissonAutomorphyGaussianParabolic.poisson_summation_and_rational_theta_automorphy D γ

end OAI.RepresentationTheory.Hecke.Analytic.GaloisValuation
