import OAI.NumberTheory.PadicHodge.GeometricComparison.Completion
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntrinsicWeil

/-! # Completion Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CompletionIntrinsic

/-! Discharge the exact geometric weight input using the native
Completion theorem under its original natural hypotheses. -/

universe u

theorem nativeGeometricWeightInput : Completion.GeometricWeightInput :=
  AlgebraicGeometry.FormalGeometry.Completion.IntrinsicWeil.Construction.geometric_h1_frobenius_absolute_values

end OAI.NumberTheory.PadicHodge.GeometricComparison.CompletionIntrinsic
