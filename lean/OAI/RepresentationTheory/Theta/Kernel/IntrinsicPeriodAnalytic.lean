import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGeometricPolynomial
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph

/-! # Intrinsic Period Analytic -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodAnalytic.Intrinsic

noncomputable section

/-! The native period itself is an explicit quotient of polynomial
Hodge-graph matrices, hence has an ambient analytic extension locally
at every ball point. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise ContDiff

open Filter
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGeometricPolynomial.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def periodPolynomialRatio (z : Fin 2 → ℂ) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicGeometricPolynomial.Intrinsic.momentumPolynomial A B z * (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial A B z)⁻¹

theorem periodPolynomialRatio_ball (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    periodPolynomialRatio B z.val = (B.period z).matrix := by
  unfold periodPolynomialRatio
  rw [IntrinsicGeometricPolynomial.Intrinsic.momentumPolynomial_ball A B hG z,IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_ball A B hG z,
    Matrix.inv_eq_left_inv (B.frame z).inv_val,Matrix.mul_assoc,(B.frame z).val_inv,Matrix.mul_one]

theorem periodPolynomialRatio_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    ContDiffAt ℂ ⊤ (periodPolynomialRatio B) z.val := by
  have hd : (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial A B z.val).det ≠ 0 := by
    rw [IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_ball A B hG z,← (hG.2.2.2.2.2.1 z).2]
    exact pow_ne_zero 2 (hG.2.2.2.2.2.1 z).1
  exact IntrinsicMatrixAnalytic.Intrinsic.matrix_product_contDiffAt _ _ (IntrinsicGeometricPolynomial.Intrinsic.momentumPolynomial_analytic A B).contDiffAt
    (IntrinsicMatrixAnalytic.Intrinsic.matrix_inverse_contDiffAt _ (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_analytic A B).contDiffAt hd)

theorem periodExtension_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.Intrinsic.periodExtension B) z.val := by
  apply (periodPolynomialRatio_analytic B hG z).congr_of_eventuallyEq
  filter_upwards [IntrinsicSmooth.IntrinsicSections.ballDomain_open.mem_nhds (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)] with w hw
  change (if hz : w ∈ Adelic.BallGeometryData.ballDomain then (B.period ⟨w,hz⟩).matrix else 0) = periodPolynomialRatio B w
  rw [dite_eq_left hw]
  exact (periodPolynomialRatio_ball B hG ⟨w,hw⟩).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodAnalytic.Intrinsic
