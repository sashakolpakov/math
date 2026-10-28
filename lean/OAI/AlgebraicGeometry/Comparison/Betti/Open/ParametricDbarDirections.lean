import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricTailCauchy
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionDirections
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesDirectionalDerivative

/-! # Parametric Dbar Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarDirections.Dolbeault

noncomputable section

/-! The actual global complex-line primitive preserves every holomorphic
parameter direction throughout the original open parameter domain. -/

open _root_.TopologicalSpace Set _root_.Complex
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem openParametricCauchyCandidate_preserves_holomorphic_direction
    (S : Opens P) (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg) q (I • v, 0) =
      I • fderiv ℝ (ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg) q (v, 0) := by
  have hpoint : ((S : Set P) ×ˢ univ) ∈ nhds q :=
    (S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩
  have h0 := ((ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg 0).contDiffAt hpoint).differentiableAt (by simp)
  have hs := ((ParametricTailCauchy.Dolbeault.correctedOpenParametricCauchySeries_smooth S g hg).contDiffAt hpoint).differentiableAt (by simp)
  have he : fderiv ℝ (ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg) q =
      fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0) q +
        fderiv ℝ (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) q :=
    (h0.hasFDerivAt.add hs.hasFDerivAt).fderiv
  rw [he, add_apply, add_apply,
    ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_preserves_direction_on S.isOpen hg 0 q hq v hv,
    ParametricSeriesDirectionalDerivative.Dolbeault.correctedOpenParametricCauchySeries_parameter_fderiv S g hg q hq (I • v),
    ParametricSeriesDirectionalDerivative.Dolbeault.correctedOpenParametricCauchySeries_parameter_fderiv S g hg q hq v]
  have hsum : (∑' n, fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (I • v, 0)) =
      I • ∑' n, fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (v, 0) := by
    simp_rw [ParametricCorrectionDirections.Dolbeault.correctedOpenParametricCauchyDifference_preserves_direction S g hg _ q hq v hv]
    exact tsum_const_smul'' I
  rw [hsum, smul_add]

theorem exists_open_parametric_vectorDbar_primitive_preserving_directions
    (S : Opens P) {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) :
    ∃ G : P × ℂ → F, ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ univ) ∧
      (∀ p ∈ S, ∀ z : ℂ, VectorDbar.Dolbeault.vectorDbar (fun w => G (p, w)) z = g (p, z)) ∧
      ∀ (q : P × ℂ), q.1 ∈ S → ∀ v : P,
        (∀ w : ℂ, fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) →
        fderiv ℝ G q (I • v, 0) = I • fderiv ℝ G q (v, 0) :=
  ⟨ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg, ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S g hg,
    fun _ hp z => ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_dbar S g hg hp z,
    openParametricCauchyCandidate_preserves_holomorphic_direction S g hg⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricDbarDirections.Dolbeault
