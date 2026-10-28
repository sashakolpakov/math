import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarDirections
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionKernels

/-! # Parametric Dbar Kernels -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarKernels.Dolbeault

noncomputable section

/-! Preservation of all complex-linear coefficient kernels by the
actual global line primitive over an open parameter domain. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

variable {P F G : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [CompleteSpace G]

theorem openParametricCauchyCandidate_kernel (L : F →L[ℂ] G) (S : Opens P)
    (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (q : P × ℂ) (hq : q.1 ∈ S)
    (hzero : ∀ w : ℂ, L (g (q.1, w)) = 0) :
    L (ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg q) = 0 := by
  change L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0 q +
    ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q) = 0
  rw [map_add, ParametricCorrectionKernels.Dolbeault.expandingParametricCauchyPrimitive_kernel_on L S hg 0 q hq hzero,
    L.map_tsum (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricCauchyDifference_summable (q := q) S g hg hq), zero_add]
  have he : (fun n => L (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q)) = fun _ => (0 : G) :=
    funext (fun n => ParametricCorrectionKernels.Dolbeault.correctedOpenParametricCauchyDifference_kernel L S g hg n q hq hzero)
  rw [he, tsum_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarKernels.Dolbeault
