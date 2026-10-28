import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCauchyCorrections
import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections

/-! # Parametric Correction Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionDirections.Dolbeault

noncomputable section

/-! Each actual correction over an open parameter domain preserves
every holomorphic parameter direction of the original input family. -/

open _root_.TopologicalSpace Set _root_.Complex
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P] in
theorem expandingParametricCauchyDifference_preserves_direction_on (S : Opens P)
    {g : P × ℂ → F} (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) q (I • v, 0) =
      I • fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) q (v, 0) := by
  have hpoint : ((S : Set P) ×ˢ univ) ∈ nhds q :=
    (S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩
  have he : fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) q =
      fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g (n + 1)) q -
        fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n) q :=
    (((ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg (n + 1)).contDiffAt hpoint).differentiableAt (by simp)).hasFDerivAt.sub
        (((ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg n).contDiffAt hpoint).differentiableAt (by simp)).hasFDerivAt |>.fderiv
  rw [he, sub_apply, sub_apply,
    ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_preserves_direction_on S.isOpen hg (n + 1) q hq v hv,
    ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_preserves_direction_on S.isOpen hg n q hq v hv, smul_sub]

theorem openParametricCauchyCorrectionPolynomial_preserves_direction
    (S : Opens P) (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n) q (I • v, 0) =
      I • fderiv ℝ (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n) q (v, 0) := by
  apply CauchyPolynomialDirections.Dolbeault.cauchyParameterPolynomial_preserves_holomorphic_direction (S.isOpen.prod isOpen_univ)
    (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n) S.isOpen hq
    (ParametricCorrectionOrders.Dolbeault.parametricCorrectionRadius_pos n) (prod_mono Subset.rfl (subset_univ _))
  intro w hw
  exact expandingParametricCauchyDifference_preserves_direction_on S hg n (q.1, w) hq v hv

theorem correctedOpenParametricCauchyDifference_preserves_direction
    (S : Opens P) (g : P × ℂ → F) (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ))
    (n : ℕ) (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (I • v, 0) =
      I • fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (v, 0) := by
  have hpoint : ((S : Set P) ×ˢ univ) ∈ nhds q :=
    (S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩
  have hd := ((ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n).contDiffAt hpoint).differentiableAt (by simp)
  have hp := ((ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial_smooth S g hg n).contDiffAt hpoint).differentiableAt (by simp)
  have he : fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q =
      fderiv ℝ (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n) q -
        fderiv ℝ (ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n) q :=
    (hd.hasFDerivAt.sub hp.hasFDerivAt).fderiv
  rw [he, sub_apply, sub_apply,
    expandingParametricCauchyDifference_preserves_direction_on S hg n q hq v hv,
    openParametricCauchyCorrectionPolynomial_preserves_direction S g hg n q hq v hv, smul_sub]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricCorrectionDirections.Dolbeault
