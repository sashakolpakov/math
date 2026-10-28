import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothHolomorphicScalar
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogNorm

/-! # Scalar Open Connection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection

noncomputable section

section

/-! The actual local curvature operator annihilates holomorphic logarithms and their conjugates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U V : Opens M}

def smoothScalarOpenCurvature (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)))

theorem smoothScalarOpenCurvature_add (f g : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    smoothScalarOpenCurvature (f + g) = smoothScalarOpenCurvature f + smoothScalarOpenCurvature g := by
  have h := (SmoothScalarForm.smoothScalarOpenZeroFormLinear (E := E) U).map_add f g
  change SmoothScalarForm.smoothScalarOpenZeroForm (f + g) = SmoothScalarForm.smoothScalarOpenZeroForm f + SmoothScalarForm.smoothScalarOpenZeroForm g at h
  unfold smoothScalarOpenCurvature
  rw [h, map_add, map_add, map_add]

theorem smoothScalarOpenCurvature_restrict (h : V ≤ U) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (smoothScalarOpenCurvature f) =
      smoothScalarOpenCurvature (SmoothScalarForm.smoothComplexOpenFunctionRestrict h f) := by
  simp only [smoothScalarOpenCurvature, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d,
    Manifold.OneFormProjection.openManifoldOnePart_restrict, SmoothScalarForm.smoothScalarOpenZeroForm_restrict]

theorem smoothScalarOpenCurvature_holomorphic (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    smoothScalarOpenCurvature (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) = 0 := by
  rw [smoothScalarOpenCurvature, SmoothHolomorphicScalar.smoothHolomorphicScalar_holomorphicPart_d]
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared _

theorem smoothScalarOpenCurvature_conjugateHolomorphic (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    smoothScalarOpenCurvature (SmoothHolomorphicScalar.conjugateSmoothOpenFunction (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g)) = 0 := by
  rw [smoothScalarOpenCurvature, SmoothHolomorphicScalar.smoothConjugateHolomorphicScalar_holomorphicPart_d, map_zero]

theorem smoothScalarOpenCurvature_logNormSq_exp (l : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, f x = (Real.log (Complex.normSq (Complex.exp (l x))) : ℂ)) :
    smoothScalarOpenCurvature f = 0 := by
  have h : f = SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l +
      SmoothHolomorphicScalar.conjugateSmoothOpenFunction (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l) := by
    apply ContMDiffMap.ext
    intro x
    exact (hf x).trans (Holomorphic.LogNorm.complexLog_normSq_exp (l x))
  rw [h, smoothScalarOpenCurvature_add, smoothScalarOpenCurvature_holomorphic,
    smoothScalarOpenCurvature_conjugateHolomorphic, add_zero]

end

/-! The actual scalar connection operator and its logarithmic primitive formula. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {U V : Opens M}

def smoothScalarOpenConnection (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 :=
  Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f))

theorem smoothScalarOpenConnection_add (f g : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    smoothScalarOpenConnection (f + g) = smoothScalarOpenConnection f + smoothScalarOpenConnection g := by
  have h := (SmoothScalarForm.smoothScalarOpenZeroFormLinear (E := E) U).map_add f g
  change SmoothScalarForm.smoothScalarOpenZeroForm (f + g) = SmoothScalarForm.smoothScalarOpenZeroForm f + SmoothScalarForm.smoothScalarOpenZeroForm g at h
  unfold smoothScalarOpenConnection
  rw [h, map_add, map_add]

theorem smoothScalarOpenConnection_restrict (h : V ≤ U) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (smoothScalarOpenConnection f) =
      smoothScalarOpenConnection (SmoothScalarForm.smoothComplexOpenFunctionRestrict h f) := by
  simp only [smoothScalarOpenConnection, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d,
    Manifold.OneFormProjection.openManifoldOnePart_restrict, SmoothScalarForm.smoothScalarOpenZeroForm_restrict]

theorem smoothScalarOpenConnection_logNormSq_exp (l : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, f x = (Real.log (Complex.normSq (Complex.exp (l x))) : ℂ)) :
    smoothScalarOpenConnection f = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  have h : f = SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l +
      SmoothHolomorphicScalar.conjugateSmoothOpenFunction (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l) := by
    apply ContMDiffMap.ext
    intro x
    exact (hf x).trans (Holomorphic.LogNorm.complexLog_normSq_exp (l x))
  rw [h, smoothScalarOpenConnection_add]
  change Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l))) +
    Manifold.OneFormProjection.openManifoldOnePart (-Complex.I) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
      (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.conjugateSmoothOpenFunction (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)))) = _
  rw [SmoothHolomorphicScalar.smoothHolomorphicScalar_holomorphicPart_d, SmoothHolomorphicScalar.smoothConjugateHolomorphicScalar_holomorphicPart_d, add_zero]

theorem smoothScalarOpenConnection_log_difference (l : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (f h : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hf : ∀ x : U, (f - h) x = (Real.log (Complex.normSq (Complex.exp (l x))) : ℂ)) :
    smoothScalarOpenConnection f = smoothScalarOpenConnection h +
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen l)) := by
  have he : f = (f - h) + h := (sub_add_cancel f h).symm
  conv_lhs => rw [he]
  rw [smoothScalarOpenConnection_add, smoothScalarOpenConnection_logNormSq_exp l (f - h) hf, add_comm]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection
