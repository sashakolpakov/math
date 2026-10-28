import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCycleWeights

/-! # Zero Cycle Model -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCycleModel.Dolbeault

noncomputable section

/-! The original additive Laurent zero cycles are the existing algebraic Laurent zero cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveLaurentZeroCyclesEquiv (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).d 0 1).hom.ker ≃+
      SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 1)) d where
  toFun z := ⟨z.val, by
    have hz := z.property
    change (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d).d 0 1 z.val = 0 at hz
    rw [SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d] at hz
    exact hz⟩
  invFun z := ⟨z.val, by
    change (SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := ℂ) j d).d 0 1 z.val = 0
    rw [SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex_d]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem projectiveLaurentZeroCyclesEquiv_val (n : ℕ) (j : Fin (n + 1)) (d : ℤ)
    (z : ((LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j d).d 0 1).hom.ker) :
    (projectiveLaurentZeroCyclesEquiv n j d z).val = z.val := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCycleModel.Dolbeault
