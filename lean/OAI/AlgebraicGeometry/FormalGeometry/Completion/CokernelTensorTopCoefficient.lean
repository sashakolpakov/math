import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentCokernelTensor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialTopCoefficient

/-! # Cokernel Tensor Top Coefficient -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CokernelTensorTopCoefficient

noncomputable section

/-! The top coefficients of a coherent exact-sequence difference are
unchanged when the entire sequence is tensored by any line bundle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [Infinite K] {r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem coherentCokernelTensor_coeff_eq
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ N) [Mono a] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) (d : ℕ)
    (hd : (ClosedHilbertAdditivity.Construction.closedProjectiveCokernelHilbertPolynomial f a j).natDegree ≤ d) :
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor N L) j -
      ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).coeff d =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f N j - ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).coeff d := by
  have hh := IntegralProjectiveNumerics.Construction.integralClosedProjective_coherentLineBundle_hilbert_degree_leadingCoeff
    f (CoherentCokernelTensor.Construction.coherentModuleCokernel a) L j
  rw [← CoherentCokernelTensor.Construction.coherentCokernelTensor_hilbertPolynomial f a L j,
    ← ClosedHilbertAdditivity.Construction.closedProjectiveCokernelHilbertPolynomial_eq_sub f a j]
  apply PolynomialTopCoefficient.Construction.polynomial_coeff_eq_of_same_leading_data _ _ hh.1 hh.2 d
  exact hh.1.trans_le hd

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CokernelTensorTopCoefficient
