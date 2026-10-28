import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator

/-! # Rough Anti -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

noncomputable section

section

/-! The antiholomorphic covariant rough Laplacian is the actual negative tensor divergence, with its exact Hessian trace. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def lineCovectorAntiDerivative (n : ℕ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x)

def lineCovectorRoughLaplacian (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  -TensorMetricTest.lineCovectorTensorDivergence b n B G A (lineCovectorAntiDerivative n G A a) x

omit [LinearOrder ι] in
theorem lineCovectorRoughLaplacian_hessian (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (ha : DifferentiableAt ℝ (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x)
    (hG : ∀ v w, G x v (Complex.I • w) = Complex.I • G x v w) :
    lineCovectorRoughLaplacian b n B G A a x =
      -(1 / 2 : ℂ) • ∑ i, (CovectorHessian.lineCovectorHessian n G A a x (b i)
        (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) +
        Complex.I • CovectorHessian.lineCovectorHessian n G A a x (b i)
          (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) := by
  unfold lineCovectorRoughLaplacian TensorMetricTest.lineCovectorTensorDivergence lineCovectorAntiDerivative
  simp only [Cutoff.lineCovectorTensorDerivative_antilinear n G A _ ha _ (hG _),
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, HessianBilinear.lineCovectorTensorDerivative_hessian n G A a ha,
    ← Finset.smul_sum, neg_smul]

end

section

/-! The full real covariant Hessian trace and its genuine zeroth-order curvature trace. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]

def lineCovectorFullRoughLaplacian (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  -∑ j, CovectorHessian.lineCovectorHessian n G A a x (b j) (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord j).toContinuousLinearMap)

theorem lineCovectorFullRoughLaplacian_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (t : Fin n → E) :
    lineCovectorFullRoughLaplacian b n B G A a x t =
      -∑ j, CovectorHessian.lineCovectorHessian n G A a x (b j) (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord j).toContinuousLinearMap) t := by
  simp only [lineCovectorFullRoughLaplacian, ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.sum_apply]

variable [NormedSpace ℂ E]

def lineCovectorMixedCurvatureTrace (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  ∑ j, (-Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)) a +
    F ![b j, Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap] • a)

theorem lineCovectorMixedCurvatureTrace_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (R : E → E → E →L[ℝ] E) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (t : Fin n → E) :
    lineCovectorMixedCurvatureTrace b n B R F a t =
      ∑ j, (-Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (R (b j) (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)) a +
        F ![b j, Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap] • a) t := by
  simp only [lineCovectorMixedCurvatureTrace, ContinuousAlternatingMap.sum_apply]

end

/-! Local replacement of fields preserves the original covariant Hessian and full real rough Laplacian. -/

open Filter
open scoped _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionDerivative_eventually_congr (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a b : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (hab : a =ᶠ[𝓝 x] b) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a =ᶠ[𝓝 x] ConnectionSymbols.lineCovectorConnectionDerivative n G A b := by
  filter_upwards [hab.eventuallyEq_nhds] with y hy
  exact Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr n G A a b hy

theorem lineCovectorHessian_congr (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a b : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (hab : a =ᶠ[𝓝 x] b) (v w : E) :
    CovectorHessian.lineCovectorHessian n G A a x v w = CovectorHessian.lineCovectorHessian n G A b x v w := by
  have hc : (fun y => ConnectionSymbols.lineCovectorConnectionDerivative n G A a y w) =ᶠ[𝓝 x]
      (fun y => ConnectionSymbols.lineCovectorConnectionDerivative n G A b y w) :=
    (lineCovectorConnectionDerivative_eventually_congr n G A a b hab).mono
      (fun _ hy => congrArg (fun L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n => L w) hy)
  unfold CovectorHessian.lineCovectorHessian
  rw [Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr n G A _ _ hc,
    Holomorphic.AdjointDerivative.lineCovectorConnectionDerivative_congr n G A a b hab]

end

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]

theorem lineCovectorFullRoughLaplacian_congr (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (hac : a =ᶠ[𝓝 x] c) :
    lineCovectorFullRoughLaplacian b n B G A a x = lineCovectorFullRoughLaplacian b n B G A c x := by
  unfold lineCovectorFullRoughLaplacian
  exact congrArg Neg.neg (Finset.sum_congr rfl (fun j _ => lineCovectorHessian_congr n G A a c hac _ _))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti
