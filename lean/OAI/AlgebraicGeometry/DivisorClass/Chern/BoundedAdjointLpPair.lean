import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Bounded Adjoint Lp Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BoundedAdjointLpPair

noncomputable section

/-! The compact adjoint test for the original principal coefficient pairs exactly with any actual bounded extension agreeing on its test support. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction

theorem compactAdjointSchwartz_bounded_energy_pair {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E → F →L[ℝ] F) (q : 𝓢(E, F)) {U : Set E}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hq : HasCompactSupport q) (hs : tsupport q ⊆ U)
    (B : E → F →L[ℝ] F) (hBm : AEStronglyMeasurable B volume) {K : ℝ}
    (hB : ∀ᵐ x ∂(volume : Measure E), ‖B x‖ ≤ K)
    (hBA : ∀ x ∈ tsupport q, B x = A x) (a : Lp F 2 (volume : Measure E)) :
    inner ℝ a ((Compact.Adjoint.compactAdjointSchwartz A q hU hA hq hs).toLp 2 volume) =
      ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy B hBm hB a (q.toLp 2 volume) :=
  Compact.Adjoint.compactAdjointSchwartz_L2_pair A q hU hA hq hs a (ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp B hBm hB a)
    ((ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp_coe B hBm hB a).mono (fun x hx hqx =>
      hx.trans (congrArg (fun T : F →L[ℝ] F => T (a x)) (hBA x hqx))))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BoundedAdjointLpPair
