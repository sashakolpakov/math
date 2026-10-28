import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Comparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison

/-! # Comparison Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonJets.CM

noncomputable section

/-! All completed Taylor tensors retain the exact finite-input comparison;
no coefficient or projection is selected in these identities. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W}
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A)

theorem comparison_input_completed_theta_jets (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C (Comparison.CM.comparisonFiniteInput C φ) Z.matrix) 0 u =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 u :=
  congrArg (fun f => iteratedFDeriv ℂ a f 0 u)
    (funext (fun ξ => Comparison.CM.comparison_input_completed_theta C φ Z ξ))

theorem comparison_source_completed_theta_jets
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f Z.matrix) 0 u =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (Comparison.CM.comparisonSourceInput C f) Z) 0 u :=
  congrArg (fun f => iteratedFDeriv ℂ a f 0 u)
    (funext (fun ξ => Comparison.CM.comparison_source_completed_theta C f Z ξ))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonJets.CM
