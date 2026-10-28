import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartDifferenceCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FiberCoefficientDerivationKernel

/-! # Transition Linear Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.TransitionLinearComparison

noncomputable section

/-! Actual product-chart transitions agree with the constructed linear
fiber derivations when their original affine functions recover the chosen
linear lift coefficients. -/

open scoped TensorProduct

variable (k R S B : Type) [CommRing k] [CommRing R] [CommRing S] [CommRing B]
    [Algebra k R] [Algebra k S] [Algebra k B] [Algebra R k] [Algebra R S] [Algebra R B] [Algebra S B]
    [IsScalarTower k R S] [IsScalarTower k R B] [IsScalarTower k S B]
    [IsScalarTower R k B] [IsScalarTower R S B] [Algebra.IsPushout R k S B]
    {V : Type} [AddCommGroup V] [Module k V]
    (L M : V →ₗ[k] Derivation k S B)
    (h : ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S B).restrictScalars k).comp L =
      ((Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k R S B).restrictScalars k).comp M)

local instance transitionLinearComparison_commRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

theorem productTransition_eq_linearFiberDifference
    {P : Type} [CommRing P] [Algebra (DualNumber k) P] (q : P →+* B)
    (f g : P ≃ₐ[DualNumber k] (DualNumber k ⊗[k] B))
    (hf : ∀ p, Dual.TensorReduction.dualTensorReduction k B (f p) = q p)
    (hg : ∀ p, Dual.TensorReduction.dualTensorReduction k B (g p) = q p)
    (j : S →+* P) (hj : ∀ s, q (j s) = algebraMap S B s) (v : V)
    (hL : ∀ s, (Dual.NumberCoefficients.dualTensorCoefficientEquiv k B (f (j s))).snd = L v s)
    (hM : ∀ s, (Dual.NumberCoefficients.dualTensorCoefficientEquiv k B (g (j s))).snd = M v s) :
    Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg = FiberCoefficientDerivationKernel.linearFiberLiftDifference k R S B B L M h v := by
  apply BaseChangedCoefficientDerivations.baseChangedCoefficientDerivation_ext R k S B B
  intro s
  rw [FiberCoefficientDerivationKernel.linearFiberLiftDifference_algebraMap, ← hj s,
    ChartDifferenceCoefficients.dualProductChartDifference_coefficients, hM s, hL s]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.TransitionLinearComparison
