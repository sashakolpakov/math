import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicTwoCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo

/-! # Closed Two Derivatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosedTwoDerivatives.Closedness

noncomputable section

/-! Closed forms of type (2,0) have genuinely holomorphic coefficients. -/

open Filter OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem type20_fderiv (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E} (hf : DifferentiableAt ℝ f x)
    (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (f y)) (u : E) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (fderiv ℝ f x u) := by
  intro z v
  have heq : (fun y => f y (fun i => (z : ℂ) • v i)) =ᶠ[𝓝 x]
      (fun y => Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 2 0 z * f y v) := by
    filter_upwards [ht] with y hy
    exact hy z v
  have h := congrArg (fun L : E →L[ℝ] ℂ => L u) heq.fderiv_eq
  rw [fderiv_continuousAlternatingMap_apply_const_apply hf,
    fderiv_const_mul (hf.continuousAlternatingMap_apply_const v)] at h
  simpa only [smul_apply, smul_eq_mul, fderiv_continuousAlternatingMap_apply_const_apply hf] using h

omit [IsScalarTower ℝ ℂ E] in
theorem closed_type20_firstDerivative_J (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (f y))
    (hc : extDeriv f x = 0) (u v w : E) :
    ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative f x (Complex.I • u) v w =
      Complex.I * ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative f x u v w := by
  have hJ (a b c : E) : ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative f x a (Complex.I • b) c =
      Complex.I * ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative f x a b c :=
    HolomorphicTwoCoefficient.Closedness.twoFormBilinear_type20_J_left _ (type20_fderiv f hf ht a) b c
  have h := ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative_closed f hf hc (Complex.I • u) v w
  rw [hJ, hJ] at h
  have h' := ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative_closed f hf hc u v w
  linear_combination h - Complex.I * h'

omit [IsScalarTower ℝ ℂ E] in
theorem closed_type20_antiholomorphic_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (f y))
    (hc : extDeriv f x = 0) (u v w : E) :
    ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear (f y) v w) x u = 0 := by
  simp only [ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply]
  rw [ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, ← ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative_apply f hf,
    ← ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction.twoFormFirstDerivative_apply f hf, closed_type20_firstDerivative_J f hf ht hc]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, mul_zero]

theorem closed_type20_coefficient_antiholomorphic_derivative
    (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (f y))
    (hc : extDeriv f x = 0) (u v w : E) :
    ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (f y) v w) x u =
      0 := by
  have heq : (fun y => HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient (f y) v w) =ᶠ[𝓝 x]
      (fun y => ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear (f y) v w) := by
    filter_upwards [ht] with y hy
    exact HolomorphicTwoCoefficient.Closedness.holomorphicTwoCoefficient_type20 (f y) hy v w
  unfold ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
  rw [heq.fderiv_eq]
  exact closed_type20_antiholomorphic_derivative f hf ht hc u v w

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosedTwoDerivatives.Closedness
