import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCauchyCorrections
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections
import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyLocalNaturality

/-! # Parametric Correction Kernels -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionKernels.Dolbeault

noncomputable section

/-! The actual open-domain corrections preserve each complex-linear
coefficient kernel on every complete input slice. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F G : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] [CompleteSpace G]

theorem expandingParametricCauchyPrimitive_kernel_on (L : F →L[ℂ] G) (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S)
    (hzero : ∀ w : ℂ, L (g (q.1, w)) = 0) : L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n q) = 0 :=
  VectorCauchyLocalNaturality.Dolbeault.localizedVectorCauchyTransform_kernel L (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).contDiff
    (ExpandingCauchyPrimitives.Dolbeault.expandingCauchyBump n).hasCompactSupport (g := fun p z => g (p, z))
    S.isOpen isOpen_univ (subset_univ _) hg q hq (fun w _ => hzero w)

theorem expandingParametricCauchyDifference_kernel_on (L : F →L[ℂ] G) (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S)
    (hzero : ∀ w : ℂ, L (g (q.1, w)) = 0) : L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n q) = 0 := by
  change L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g (n + 1) q - ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n q) = 0
  rw [map_sub, expandingParametricCauchyPrimitive_kernel_on L S hg (n + 1) q hq hzero,
    expandingParametricCauchyPrimitive_kernel_on L S hg n q hq hzero, sub_self]

variable [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

theorem openParametricCauchyCorrectionPolynomial_kernel (L : F →L[ℂ] G) (S : Opens P)
    (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (hzero : ∀ w : ℂ, L (g (q.1, w)) = 0) :
    L (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n q) = 0 := by
  let N := Classical.choose (ParametricCauchyCorrections.Dolbeault.exists_openParametricCorrectionOrder S hg n)
  have hc : ContinuousOn (fun z => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (q.1, z))
      (sphere 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n : ℝ)) :=
    (ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n) hq).continuous.continuousOn
  have hm : L (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n q) =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun y => L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n y))
        0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n) N q :=
    CauchyPolynomialNaturality.Dolbeault.cauchyPowerSeries_partialSum_map L (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius_pos n) hc N q.2
  rw [hm]
  calc
    _ = Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial (fun _ => (0 : G)) 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n) N q :=
      CauchyPolynomialDirections.Dolbeault.cauchyParameterPolynomial_circle_congr (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius_pos n).le
        (fun z _ => expandingParametricCauchyDifference_kernel_on L S hg n (q.1, z) hq hzero) N
    _ = 0 := CauchyPolynomialDirections.Dolbeault.cauchyParameterPolynomial_zero 0 (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius n) N q

theorem correctedOpenParametricCauchyDifference_kernel (L : F →L[ℂ] G) (S : Opens P)
    (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (hzero : ∀ w : ℂ, L (g (q.1, w)) = 0) :
    L (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q) = 0 := by
  change L (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n q - ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n q) = 0
  rw [map_sub, expandingParametricCauchyDifference_kernel_on L S hg n q hq hzero,
    openParametricCauchyCorrectionPolynomial_kernel L S g hg n q hq hzero, sub_self]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionKernels.Dolbeault
