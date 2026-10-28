import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointDerivative
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTraceTransport
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CovectorCommutator

/-! # Covector Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorHessian

noncomputable section

/-! The covariant Hessian and the derivative of the actual metric trace. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lineCovectorHessian (n : ℕ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v w : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => ConnectionSymbols.lineCovectorConnectionDerivative n G A a y w) x v -
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a x (G x v w)

theorem lineCovectorHessian_commutator_one
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hG : DifferentiableAt ℝ G x) (hA : DifferentiableAt ℝ A x) (ha : ContDiffAt ℝ ∞ a x)
    (hGs : ∀ v w, G x v w = G x w v) (v w : E) :
    lineCovectorHessian 1 G A a x v w - lineCovectorHessian 1 G A a x w v =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x v w) (a x) +
        (fderiv ℝ A x v w - fderiv ℝ A x w v) • a x := by
  unfold lineCovectorHessian
  rw [hGs v w]
  convert! Holomorphic.CovectorCommutator.lineCovectorConnectionDerivative_commutator_one G A a hG hA ha v w using 1
  abel

end Linear

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem lineCovariantCodifferential_hessian (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (v : E)
    (hmetric : ∀ p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (ConnectionSymbols.lineCovariantCodifferential b n B G A a) x v =
      -∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
        (lineCovectorHessian (n + 1) G A a x v (b i)) := by
  rw [CovectorNeg.lineCovariantCodifferential_derivative b n B G A a hU hB hG hA ha hpos hx v hmetric,
    CovectorTraceTransport.covector_trace_basis_transport b n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x)) (G x v)
      (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a x)]
  simp only [lineCovectorHessian, map_sub, Finset.sum_sub_distrib]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorHessian
